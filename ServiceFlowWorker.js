'use strict';

require("./Extensions.js");
const fs = require("fs");

const async       = require('async');
const DynatraceUI = require('./DynatraceUI.js');
const DatabaseTracker = require('./DatabaseTracker.js');

const serviceMethodMetricMappings = require("../config/serviceMethodMetricMappings.json");

const maxDisplayNameSize = 512;
const maxStringValueSize = 256;
const oneHour = 60 * 60 * 1000;

// This list only contains granularities that the Dynatrace API accepts.
const granularities = [
    { label: "minute",     value: "_min",    bucket: 1
 }, { label: "5 minutes",  value: "_5mins",  bucket: 5
 }, { label: "10 minutes", value: "_10mins", bucket: 10
 }, { label: "15 minutes", value: "_15mins", bucket: 15
 }, { label: "30 minutes", value: "_30mins", bucket: 30
 }, { label: "hourly",     value: "_hour",   bucket: 60
 }, { label: "2 hours",    value: "_2hours", bucket: 60*2
 }, { label: "6 hours",    value: "_6hours", bucket: 60*6
 }, { label: "daily",      value: "_day",    bucket: 60*24
 }
];
const timespans = granularities.reduce(function(result, granularity) {
     result[granularity.value] = granularity.bucket * 60 * 1000;
     return result;
}, {});

let serviceConfig = {};
let tuningInfo    = { maxThreads: 8 };
let dynatraceUI   = null;
let jobCount = 0;
let jobQueue = [];
let database = null;

const logger = {
    log:   function (job, message, severity) {
        if (!job)
            return console.log(severity + ": " + message);

        job.log = job.log || {};
        job.log.messages = job.log.messages || [];
        job.log.summary  = job.log.summary  || {}
        job.log.summary.errors = job.log.summary.errors || [];

        job.log.messages.push((severity || "INFO") + ": " + message);
    },
    info:  function (job, message) {
        this.log(job, message, "INFO");
    },
    warn:  function (job, message) {
        this.log(job, message, "WARNING");
    },
    error: function (job, message) {
        this.log(job, message, "ERROR");
    },
    errors: function (job, max) {
        let errorCount = 0;
        let errors = [];

        job.log.messages = job.log.messages.filter(message => {
            if (message.indexOf("ERROR") === 0) {
                if (errors.length < (max || 1))
                    errors.push(message);

                errorCount++;
                return false;
            }
            else {
                return true;
            }
        });
        if (errors.length < errorCount)
            errors.push("(" + (errorCount - errors.length) + " more)");

        return errors;
    }
};

const requestScripts = {
    appMethods: {
        url: "/rest/serviceheader/filterdata/[request.applicationId] ",
        description: "Get application methods",
        params: {
            NOTUSED: "[request.applicationId]"
        }
    },
    serviceFlows: {
        url: "/rest/serviceanalysis/serviceflow",
        description: "Get service flows for application method",
        params: {
            serviceId: "[request.applicationId]",
            analysisMode: "RESPONSE_TIME",
            sci: "[request.applicationId]",
            servicefilter: "0%1E9%11[request.transactionId]",
            timeframe: "custom[request.startTime]to[request.endTime]"
        },
        on202: {
            url: "/rest/serviceanalysis/serviceflow",
            description: "Get service flows for application method",
            params: {
                serviceId: "[request.applicationId]",
                analysisMode: "RESPONSE_TIME",
                sci: "[request.applicationId]",
                servicefilter: "0%1E9%11[request.transactionId]",
                timeframe: "custom[request.startTime]to[request.endTime]",
                prgtkn: "[response.token]"
            },
            on202: "repeat"
        }
    },
    webRequests: {
        url: "/rest/serviceanalysis/webrequests",
        description: "Get service methods for service",
        params: {
            demo: "false",
            serviceId: "[request.serviceId]",
            servicefilter: "0%1E7%11[request.applicationId]%150%150%1F9%13[request.transactionId]%15[request.servicePath]",
            gtf: "c_[request.startTime]_[request.endTime]"
        },
        on202: {
            url: "/rest/serviceanalysis/webrequests",
            params: {
                demo: "false",
                serviceId: "[request.serviceId]",
                servicefilter: "0%1E7%11[request.applicationId]%150%150%1F9%13[request.transactionId]%15[request.servicePath]",
                gtf: "c_[request.startTime]_[request.endTime]",
                prgtkn: "[response.token]"
            },
            on202: "repeat"
        }
    }
};

const applicationMethodInventory = {
    inventory: {},
    addAppMethods: function (tenant, appMethods, timestamp) {
        const tenantInventory = this.inventory[tenant] = this.inventory[tenant] || {};

        // Add methods reported by Dynatrace into the application method inventory.
        for (let i = 0; i < appMethods.length; i++) {
            const appMethod = appMethods[i];
            appMethod.timestamp = timestamp;
            tenantInventory[appMethod.transactionId] = appMethod;
        }
    },
    getAppMethods: function(tenant, applicationId) {
        const tenantInventory = this.inventory[tenant];
        if (!tenantInventory) return null;

        const appMethods = Object
            .values(tenantInventory)
            .filter(appMethod => appMethod.applicationId === applicationId);

        if (appMethods.length === 0 ||
            appMethods[0].timestamp + 60 * 60 * 100 < (new Date()).getTime())
            return null;

        return appMethods;
    }
};

function stringifyResponseError(error) {
    // Copy select things from the error. Not all of its properties are useful.
    const sanitizedError = {
        message:  error.message,
        request:  error.config,
        response: error.response ? {
            status:  error.response.status,
            message: error.response.statusText,
            headers: error.response.headers,
            data:    error.response.data
        } : "N/A"
    }
    if (sanitizedError.request) {
        delete sanitizedError.request.on202;
        delete sanitizedError.request.next;
        delete sanitizedError.request.transformRequest;
        delete sanitizedError.request.transformResponse;
    }
    return JSON.stringify(sanitizedError, null, 4);
}

function visit(root, visitor, results = [], parent = null) {
    let result = visitor(root, parent);
    result && results.push(result);

    for (let i = 0; root.children && i < root.children.length; i++) {
        visit(root.children[i], visitor, results, root);
    }
    return results;
}

function collectServiceMetrics(node) {
    const metrics = (
        ({contributionPct, callPct, callsPerRequest, avgCallTime, transactionCount, failedTransactionCount, callCount, failedCallCount}) =>
        ({contributionPct, callPct, callsPerRequest, avgCallTime, transactionCount, failedTransactionCount, callCount, failedCallCount})
        )(node);
    
    return metrics;
}

function translateRequestMetrics(metrics) {
    const add = (x, y) => x + y;
    const result = {};

    for (let metricName in serviceMethodMetricMappings) {
        const mapping = serviceMethodMetricMappings[metricName];
        if (!metrics.hasOwnProperty(metricName) || !mapping.include)
            continue;

        switch (mapping.aggregation) {
            case "NONE":
                result[mapping.name] = metrics[metricName];
                break;
            case "AVG":
                result[mapping.name] = metrics[metricName].dataPoints.map(datapoint => datapoint.value).reduce(add, 0)
                                     / (metrics[metricName].dataPoints.length || 1);
                break;
            case "SUM":
                result[mapping.name] = metrics[metricName].dataPoints.map(datapoint => datapoint.value).reduce(add, 0);
                break;
            case "MAX":
                result[mapping.name] = Math.max(...metrics[metricName].dataPoints.map(datapoint => datapoint.value));
                break;
            case "MIN":
                result[mapping.name] = Math.min(...metrics[metricName].dataPoints.map(datapoint => datapoint.value));
                break;
        }
    }
    return result;
}

function AppMethodCollector(tenant, applicationId, applicationName) {
    return onComplete => {
        // Let's see if what we have in memory, in the application method inventory.
        const appMethods = applicationMethodInventory.getAppMethods(tenant, applicationId);
        if (appMethods) {
            return onComplete(null, appMethods);
        }

        // It's not in memory or it's stale. let's check what's in the database.
        retrieveAppMethods(tenant, applicationId)
        .then(result => {
            // Add methods from the database into the application method inventory.
            applicationMethodInventory.addAppMethods(tenant, result.appMethods, result.timestamp);

            // Now let's try again to get from the application method inventory.
            const appMethods = applicationMethodInventory.getAppMethods(tenant, applicationId);
            onComplete(null, appMethods);
        })
        .catch(err => {
            // No or stale data in the database. Let's ask Dynatrace.
            dynatraceUI.scriptedRequest(
                tenant,
                requestScripts.appMethods,
                { applicationId: applicationId },
                true) // skip login - already done.
            .then(result => {
                // The result contains application methods. See page 4 of design doc.
                const appMethods = result
                    .applicationData[applicationId]
                    .applicationMethods.map(methodId => {
                        // This looks a bit screwy because most values seem to come
                        // back as arrays, even when it's always just a single value.
                        const transactionId = Array.isArray(methodId) ? methodId[0] : methodId;
                        const transactionName = result.displayNames[transactionId];

                        return {
                            applicationId:   applicationId,
                            applicationName: applicationName,
                            transactionId:   transactionId,
                            transactionName: Array.isArray(transactionName) ? transactionName[0] : transactionName
                        };
                    });

                /*  We are going to store this in the database so that on the query
                    side of things we have immediate access to it. And of course we
                    are using this also as our own 'offline' data source so that we
                    can avoid as much as possible having to ask Dynatrace.
                 */
                persistAppMethods(tenant, applicationId, applicationName, appMethods)
                .then(result => {
                    // Add methods reported by Dynatrace into the application method inventory.
                    applicationMethodInventory.addAppMethods(tenant, result.appMethods, result.timestamp);

                    // Now let's try again to get from the application method inventory.
                    const appMethods = applicationMethodInventory.getAppMethods(tenant, applicationId);
                    onComplete(null, appMethods);
                })
                .catch(error => {
                   // logger.error(job, "Could not store application methods: " + error);
                    onComplete(error);
                });
            })
            .catch(error => {
                const sanitizedError = stringifyResponseError(error);
               // logger.error(job, "Could not retrieve application methods: " + sanitizedError);
                onComplete(sanitizedError);
            });
        });
    }
}

function WebRequestsCollector(job, tenant, node, requestParams) {
    return onComplete => {
        dynatraceUI.scriptedRequest(
            tenant,
            requestScripts.webRequests,
            requestParams,
            true) // skip login - already done.
        .then(result => {
            /*  The result contains the nodes we need to insert in the tree.
                We already know where: the 'node' that we are curried with.
                See page 8 of design doc.
             */
            node.children = result.requests.map(request => ({
                type:        "SERVICE_METHOD",
                serviceId:   request.id,
                serviceName: request.name,
                serviceType: node.serviceType,
                servicePath: node.servicePath, 
                callCount:   0,
                metrics:     translateRequestMetrics(request.metrics)
            }));

            onComplete();

            fs.writeFile("../data/" + node.servicePath + "_" + requestParams.transactionId + ".json", "PARAMS: " + JSON.stringify(requestParams,null,4) + "\n RESPONSE: " + JSON.stringify(result,null,4), 'utf8', () => {});
        })
        .catch(error => {
            const sanitizedError = stringifyResponseError(error);
            logger.error(job, "Could not retrieve web requests: " + sanitizedError);

            node.children = [{
                type:        "SERVICE_METHOD",
                serviceId:   "(Unavailable)",
                serviceName: "(ERROR: " + error.message + ")",
                serviceType: node.serviceType,
                servicePath: node.servicePath, 
                callCount:   0,
                metrics:     {}
            }];

            onComplete(); // The show must go on.
        });
    }
}

function ServiceFlowsCollector(job) {
    const tenant = job.tenant || job.source;

    return new Promise((resolve, reject) => {
        dynatraceUI.scriptedRequest(
            tenant,
            requestScripts.serviceFlows,
            job,
            true) // skip login - already done.
        .then(result => {
            /*  The result should contain a tree per transaction name.
                Since the requestParams should contain a filter on transactionId,
                we would expect to find only one transaction in the result - which
                corresponds to only one property, named after the transaction name.

                Note that we already have the following info in the job:
                - applicationId
                - applicationName
                - transactionId
                - transactionName
                We'll do some sanity checks to ensure that we got the right data.
             */
            let data = null;
            if (result.root) {
                if (result.root.serviceId !== job.applicationId) {
                    console.error(result.root.serviceId + " is not the expected app ID (" + job.applicationId + ") for " + job.transactionName);

                    // And... this is also not so good. We can't use data that has bad IDs.
                    return reject(job.applicationId + " incorrect in response");
                }                  
                data = result;
            }
            else {
                const transactionNames = Object.keys(result);
                if (transactionNames.length === 0) {
                    console.error("No transactions were found in the response: " + JSON.stringify(result));

                    // Well... this is certainly not good. We can't use this data at all!
                    return reject("No transactions found in response");
                }            
                if (!result.hasOwnProperty(job.transactionName)) {
                    console.error(job.transactionName + " was not among transactions in response: " + transactionNames.join(", "));

                    // Well... this is certainly not good. We can't use this data at all!
                    return reject(job.transactionId + " not found in response");
                }
                if (result[job.transactionName].root.serviceId[0] !== job.applicationId) {
                    console.error(result[job.transactionName].root.serviceId[0] + " is not the expected app ID (" + job.applicationId + ") for " + job.transactionName);

                    // And... this is also not so good. We can't use data that has bad IDs.
                    return reject(job.applicationId + " incorrect in response");
                }
                if (transactionNames.length > 1) {
                    console.error("More than one transaction was found in the response: " + transactionNames.join(", "));

                    // But we're going to use the data anyways, because we did get the data we asked for (plus some more).
                }
                data = result[job.transactionName];
            }

            if (data.timeframe.startTime !== job.startTime) {
                console.error("Start time in response (" + data.timeframe.startTime + ") not same as requested (" + job.startTime + ")");

                // But we're going to use the data anyways. To ensure integrity, we will adopt the start time as reported.
                job.startTime = data.timeframe.startTime;
            }
            if (data.timeframe.endTime   !== job.endTime) {
                console.error("End time in response (" + data.timeframe.endTime + ") not same as requested (" + job.endTime + ")");

                // But we're going to use the data anyways. To ensure integrity, we will adopt the end time as reported.
                job.endTime = data.timeframe.endTime;
            }
            // fs.writeFile("../data/" + job.transactionId + ".json", JSON.stringify(data,null,4), 'utf8', () => {});

            // OK. Good enough. Let's absorb the tree and make it complete where necessary.
            job.serviceFlowTree = data.root;
            job.size = 0;

            //  Create all collectors we need, to complete the tree.
            job.collectors = visit(job.serviceFlowTree, (node, parent) => {
                /*  As each node in the tree is visited, we check whether that node
                    represents requests to unmonitored hosts or external services.
                    If so, we return a collector that gets the corresponding service
                    method (web request) metrics. If not, we return nothing.

                    Apparent valid criteria to recognize nodes of interest:
                        serviceName = "Requests to unmonitored hosts" OR
                                      "Requests to public networks"
                        unifiedIcon.primaryType	= "WebRequestPrivate" OR
                                                  "WebRequestPublic”"
                        xtenantService = true
                 */
                job.size++; // Count how services involved in this transaction.

                // We use 'slice' to make a copy of the service path for this node.
                node.servicePath = parent && parent.servicePath ? parent.servicePath.slice(0) : [];
                node.metrics = collectServiceMetrics(node);
                node.unifiedIcon = node.unifiedIcon || {};
                node.serviceType = node.serviceType || node.unifiedIcon.primaryType || "Unknown";

                let collector = null;
                if (node.unifiedIcon.primaryType === "WebRequestPrivate" ||
                    node.unifiedIcon.primaryType === "WebRequestPublic") {
                    collector = new WebRequestsCollector(job, tenant, node, {
                        applicationId: job.applicationId,
                        transactionId: job.transactionId,
                        serviceId:     node.serviceId,
                        servicePath:   node.servicePath.join("%150%150%1F%15") + "%150%150%1F%15",
                        startTime:     job.startTime,
                        endTime:       job.endTime
                    });
                }
                /*  We used the servicePath IDs of the services that came before us,
                    and our children will do that as well. So now is the time to add
                    our ID to the servicePath (as initialized with the parent's path).
                    NOTE: If we are the application, we add the transaction ID.
                 */
                node.servicePath.push(node.serviceId === job.applicationId ? job.transactionId : node.serviceId);

                return collector;  // This is null if there's nothing we need to do.
            });

            // Call the collectors in parallel, and wait until all missing web requests are in.
            if (job.collectors.length === 0)
              persistTree(job, data);
            else
              async.parallel(job.collectors, (err, data) => {
                // This gets called when all collectors are done (or if one reports an error).
                if (err) {
                    // On failure, retry the whole thing. All errors have been logged already.
                    // UPDATE: The collectors will never report an error - error added to data.
                    setTimeout(performJob, 2000, job, job.thread);
                }
                else {
                    /*  Note that while 'async.parallel' gives us an array of individual results
                        produced by the collectors, there is no actual data in it. At this point
                        everything has already been inserted into the service tree. We can thus
                        move on to calling 'persistTree()' to save the tree into the database.
                        Once that has been done, 'onJobProcessed()' will be called.
                     */
                    persistTree(job, data);
                }
            });

            resolve();  // We're done here. Now we have to wait until the tree is complete.
        })
        .catch(error => {
            const sanitizedError = stringifyResponseError(error);
            logger.error(job, "Could not retrieve service flows: " + sanitizedError);

            // On failure, retry the whole thing.
            setTimeout(performJob, 2000, job, job.thread);
            reject(sanitizedError);
        });
    });
}


function retrieveAppMethods(tenant, id) {
    return new Promise((resolve, reject) => {
        let sql = "SELECT TOP(1) * FROM AppMethods WHERE tenant='" + tenant + "' AND id='" + id + "'";

        this.database.connect("Retrieve app methods for " + id)
        .then(connection => {
            connection.query(sql)
            .then(rows => {
                connection.release(() => {
                    if (rows[0] && rows[0].timestamp + oneHour > (new Date().getTime()))
                        resolve({ timestamp: rows[0].timestamp, appMethods: JSON.parse(rows[0].methods) });
                    else
                        reject("No or stale data found");
                });
            })
            .catch(err => {
                // Query failed to execute. Fail.
                connection.release(() => {
                    reject(err);
                });
            });
        })
        .catch(err => {
            // No connection to the database could be created. Fail.
            reject(err);
        });
    });
}

function persistAppMethods(tenant, id, name, appMethods) {
    return new Promise((resolve, reject) => {
        database.connect("Store app methods for " + id)
        .then(async function (connection) {
            connection.begin()
            .then(() => {
                const now = (new Date()).getTime();
                const sql = "REPLACE INTO AppMethods (id, tenant, name, timestamp, methods) VALUES (?, ?, ?, ?, ?)";

                connection.query(sql, [
                    id,
                    tenant,
                    name.substring(0, maxDisplayNameSize),
                    now,
                    JSON.stringify(appMethods)
                ])
                .then(res => {
                    // Oh - good. It worked.
                    connection.commit(
                        () => resolve({ timestamp: now, appMethods: appMethods }),
                        err => reject(err)
                    );
                })
                .catch(err => {
                    // We could not insert the record.
                    connection.rollback(() => reject(err));
                });
            })
            .catch(err => {
                // We could not start a transaction.
                connection.release(() => reject(err));
            });
        })
        .catch(err => {
            // We could not obtain a connection.
            reject(err.message || err);
        });
    });
}

function persistTree(job, data, retryCount = database.retryLimit, errors = []) {

    function retry(error, insult) {
        // Let's not repeat any errors we already saw.
        if (error && !errors.includes(error))
            errors.push(error.message || error);

        // Insult on injury: an error happend WHILE we were dealing with an error!
        if (insult && !errors.includes(insult))
            errors.push(insult.message || insult);

        // if we have retries left, call ourselves after 100ms.
        if (retryCount > 0 && database.isRetryable(error)) {
            setTimeout(persistTree, 100, job, data, retryCount - 1, errors);
        }
        // If no retries left or possible, give up... :-(
        else {
            logger.error(job, "Could not persist resuls for " + job.name + ": " + errors.join(". "));

            setTimeout(onJobProcessed, 10, job);
        }
    }

    job.log.summary.collected = (new Date()).getTime();

    try {
        // See page 11 of ServiceFlow Extraction.docx.
        const records = visit(job.serviceFlowTree, node => ({
            tenant: job.tenant || job.source,
            startTime: job.startTime,
            endTime:   job.endTime,
            appMethodId:     job.transactionId,
            appMethodName:   job.transactionName,
            applicationId:   job.applicationId,
            applicationName: job.applicationName,
            id:    node.serviceId === job.applicationId ? job.transactionId    : node.serviceId,
            name:  node.serviceId === job.applicationId ? job.transactionName  : node.serviceName,
            type:  node.serviceId === job.applicationId ? "APPLICATION_METHOD" : node.type,
            icon:  node.serviceType,
            async: node.async,
            serviceType: node.serviceType,
            servicePath: node.servicePath.slice(0, -1).join("."),
            pathLength:  node.servicePath.length - 1,
            callCount:   node.callCount,
            metrics: JSON.stringify(node.metrics) 
        }));

        job.sent = records.length;

        database.connect("Store tree for " + job.transactionId)
        .then(async function (connection) {
            connection.begin()
            .then(() => {
                const keys   = Object.keys(records[0]);
                const values = records.map(record => keys.map(key => record[key]));
                const sql = 'INSERT INTO ServiceFlows (' + keys.join(',') + ') VALUES ?';

                connection.query(sql, [values])
                .then(res => {
                    // Hooray! The tree is stored!
                    connection.commit(
                        () => onJobProcessed(job),
                        (error) => retry(error)
                    );
                })
                .catch(err => {
                    // We could not store the data. Let's retry.
                    connection.rollback(
                        () => retry(err),
                        (error) => retry(err, error)
                    );
                });
            })
            .catch(err => {
                // We could not start a transaction. Let's retry.
                connection.release(() => retry(err));   // Close the connection first.
            });
        })
        .catch(err => {
            // We could not obtain a connection. Let's retry.
            retry(err.message || err);
        });
    }
    catch (ex) {
        // An exception occurred! Then fail asynchronously because
        // we don't want to inadvertently trigger premature retirement...
        logger.error(job, ex.message);

        setTimeout(onJobProcessed, 10, job);
    }
    finally {
        // Trigger next job asynchronously: it can start while this one is still
        //  busy storing data because the next job will be retrieving its data first.
        triggerNextJob(job.thread);
    }
}

function performJob(job, threadID) {
    if (!job) return;  // Should never happen, but to be sure.

    // Create a new log for this run if this is not a retry.
    if (!job.retryCount) {
        job.retryCount = 0;
        job.thread = threadID;
        job.log = {
            summary: {
                started: (new Date()).getTime(),
                errors:  []
            },
            messages: []    // For logging
        };
        // Register the execution of this job.
        jobCount++;
    }
    job.retryCount++;

    try {
        if (job.retryCount >= 5) {
            // This gets caught below and leads to the next job to be kicked off.
            throw new Error("Retry count exceeded");           
        }

        ServiceFlowsCollector(job)
        .then(() => {
            // At this point any web requests are still in the process of being collected.
            // There's nothing we need to do here.
        })
        .catch (err => {
            // If an error occurred, the serviceFlowsCollector has already initiated a retry.
            // There's nothing we need to do here.
        });
    }
    catch (ex) {
        /*  Well, this is bad... Apparently an error happened even before there has been any
            interaction with the DynatraceUI! All we can do now is log the error, call it a
            day, and give this 'thread' to the next job. Oh, wait: this can also happen when
            there have been too many retries. Same course of action.
         */
        logger.error(job, ex.message);

        setTimeout(onJobProcessed, 10, job);

        triggerNextJob(job.thread);
    }
}

function onJobProcessed(job) {
    job.log.summary.published = (new Date()).getTime();

    try {
        job.log.summary.collecting = job.log.summary.collected
                                   - job.log.summary.started;
        job.log.summary.processing = 0;
        job.log.summary.publishing = job.log.summary.published
                                   - job.log.summary.collected;
        job.log.summary.duration   = job.log.summary.published
                                   - job.log.summary.started;
        job.log.summary.errors     = logger.errors(job, 3);

        if (job.log.summary.errors &&
            job.log.summary.errors.filter(error => error.includes("Entity must not be larger than")).length > 0)
            job.log.feedback = "split";
    }
    catch (ex) {
        logger.error(job, "Error while compiling results for '" + job.name + "': " + ex);

        job.log.summary.collecting = job.log.summary.collecting || 0;
        job.log.summary.processing = job.log.summary.processing || 0;
        job.log.summary.publishing = job.log.summary.publishing || 0;
        job.log.summary.duration   = (new Date()).getTime()
                                   - job.log.summary.started;
        job.log.summary.errors     = logger.errors(job, 3);
    }
    finally {
        process.send({
            status:    job.log.summary.errors && job.log.summary.errors.length > 0 ? "failed" : "done",
            id:        job.id,
            name:      job.name,
            thread:    job.thread,
            assigned:  job.assigned,
            size:      job.size,    // No of services
            sent:      job.sent,    // No of records written
            dims:      job.dims,
            cycle:     job.cycle,
            log:       job.log,
            output:    job.output
        });
        jobCount--;
        retire();
    }
}

function triggerNextJob(threadID) {
    // Trigger next job, but create a bit of breathing room in the timing, like 2 seconds
    if (jobQueue.length > 0) {
        let job = jobQueue.pop();
        setTimeout(performJob, 2000, job, threadID);
    }
}

let waitingToRetire = false;

function retire(prepareToRetire) {
    waitingToRetire = waitingToRetire || !!prepareToRetire;

    /*  We test for both the jobCount and the jobQueue because even when the jobQueue is
        empty, not all jobs may be done. Reversely, jobCount may have returned to 0, but
        there may still be jobs waiting to be taken from the queue for processing.
     */
    if (waitingToRetire && jobCount <= 0 && jobQueue.length === 0) {
        process.disconnect();
        process.exit();
    }
}

/*  Each job can have a different destination. The configuration contains the
    list of destinations that will be used, so we will instantiate all of them.
    Each job will ask for the destination object it needs when it gets executed.
 */
process.on('message', async message => {
    switch (message.command) {
        case "configure":
            console.log("initializing");

            // DEBUG aid to give debugger time to attach:
            // TODO: Check if we are debugging.
            await new Promise(resolve => setTimeout(resolve, 3000));

            serviceConfig = message.config;
            dynatraceUI   = new DynatraceUI(serviceConfig);
            database      = new DatabaseTracker(Object.assign({
                host: "localhost",
                port: 3306,
                user: "root",
                password: "",
                database: "StreamingAPI",
                connectionLimit: 100,
                connectTimeout: 10000,
                pipelining: true
            }, serviceConfig.database), undefined, console);

            const tenantLogons = Object
                .keys(serviceConfig.Tenants)
                .map(tenant => onComplete => {
                    const creds = serviceConfig.Tenants[tenant].account.split("|");
                    dynatraceUI
                        .login(tenant, creds[0], creds[1])
                        .then( res => onComplete(null, "Successfully logged in to " + tenant))
                        .catch(err => onComplete(null, "Could not log in to " + tenant + ": " + err));
                });

            async.parallel(tenantLogons, (err, msgs) => {
                // Note that we never fail, because if one fails others may not execute.
                msgs.forEach(console.log);  // But we do log the results.

                process.send({ status: "ready" });
            });
            break;

        case "tuning":
            // Update the tuning information.
            tuningInfo = Object.assign(tuningInfo, message.tuning);
            break;

        case "perform":
            console.log("has " + message.jobs.length + " jobs for cycle " + message.cycle);

            jobQueue = [];
            // For each application in each job, get the application methods.
            // Translate those methods (transactions) into individual jobs.
            const appMethodCollectors = message.jobs.map(job => {
                job.startTime = job.endTime - timespans[job.granularity];

                return job.entities.map(entity => (function (onComplete) {
                    const appMethodCollector = new AppMethodCollector(job.tenant || job.source, entity.entityId, entity.displayName);
                    appMethodCollector((error, appMethods) => {
                        if (error)
                            console.error("    Cannot retrieve methods for " + entity.entityId);

                        onComplete(error, appMethods && appMethods.map(appMethod => {
                            const subJob = JSON.parse(JSON.stringify(job));
                            subJob.entities        = null;
                            subJob.applicationId   = appMethod.applicationId;
                            subJob.applicationName = appMethod.applicationName;
                            subJob.transactionId   = appMethod.transactionId;
                            subJob.transactionName = appMethod.transactionName;

                            return subJob;
                        }));
                    });
                }));
            }).flat();

            console.log("    which contain a total of " + appMethodCollectors.length + " applications");

            // Execute the collectors in parallel and wait until we've got all subJobs.
            async.parallel(appMethodCollectors, (err, jobs) => {
                jobQueue = jobs.flat();

                console.log("    resulting in " + jobQueue.length + " subjobs - one per transaction");

                jobQueue.splice(0, tuningInfo.maxThreads)   // Extract first batch of jobs.
                    .forEach(performJob);                   // Start them.
                // The rest of the jobs will be done, staggered, as individual jobs finish.
            });
            break;

        case "retire":
            // Terminate as soon as all jobs are complete.
            retire(true);
            break;
    }
});
process.on('disconnect', function() {
    console.log('Parent process exited - stopping ExtractionService');
    process.exit();
});

process.send({ status: "preparing" });
