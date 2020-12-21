{
	"clientLoadTotalValue": { "aggregation": "SUM", "weight": "" },
	"clientAvgLoadTime": { "aggregation": "AVG",  "weight": "" },
	"clientFailureRateAvg": { "aggregation": "AVG", "weight": "clientLoadTotalValue" },
	"clientTotalLoadPerMinValue": { "aggregation": "AVG",  "weight": "clientLoadTotalValue" },
	"clientTotalResponseTimePerMin": { "aggregation": "AVG",  "weight": "" },
	"clientResponseTimeSumValue": { "aggregation": "SUM",  "weight": "" },
	"clientResponseTimeMinValue": { "aggregation": "MIN",  "weight": "" },
	"clientResponseTimeMaxValue": { "aggregation": "MAX",  "weight": "" },
	"clientResponseTimeAvgValue": { "aggregation": "AVG",  "weight": "clientLoadTotalValue" },
	"clientFailureRate": { "aggregation": "AVG",  "weight": "" },
	"clientErrorRate": { "aggregation": "AVG",  "weight": "" },
	"clientResponseTimeP": { "aggregation": "AVG",  "weight": "" },
	"clientResponseTime50": { "aggregation": "AVG",  "weight": "" },
	"clientResponseTime90": { "aggregation": "AVG",  "weight": "" },
	"clientResponseTime95": { "aggregation": "AVG",  "weight": "" },
	"clientResponseTimeMin": { "aggregation": "AVG",  "weight": "" },
	"clientResponseTimeMax": { "aggregation": "AVG",  "weight": "" },
	"clientResponseTimeAvg": { "aggregation": "AVG",  "weight": "" },
	"serverAvgLoadTime": { "aggregation": "AVG",  "weight": "" },
	"serverLoadTotalTime": { "aggregation": "AVG",  "weight": "" },
	"serverResponseTimeP": { "aggregation": "AVG",  "weight": "" },
	"serverResponseTime50": { "aggregation": "AVG",  "weight": "" },
	"serverResponseTime90": { "aggregation": "AVG",  "weight": "" },
	"serverResponseTime95": { "aggregation": "AVG",  "weight": "" },
	"serverResponseTimeMin": { "aggregation": "AVG",  "weight": "" },
	"serverResponseTimeMax": { "aggregation": "AVG",  "weight": "" },
	"serverResponseTimeAvg": { "aggregation": "AVG",  "weight": "" },
	"serverResponseTimeSumValue": { "aggregation": "SUM",  "weight": "" },
	"serverErrorRate": { "aggregation": "AVG",  "weight": "" },
	"http4xxResponseCodes": { "aggregation": "AVG",  "weight": "" },
	"http5xxResponseCodes": { "aggregation": "AVG",  "weight": "" },
	"http4xxTotalValue": { "aggregation": "SUM",  "weight": "" },
	"http5xxTotalValue": { "aggregation": "SUM",  "weight": "" },
	"cpuTime": { "aggregation": "AVG",  "weight": "" },
	"roundTripsAvg": { "aggregation": "AVG",  "weight": "" },
	"autoLoadSumTime": { "aggregation": "SUM",  "weight": "" },
	"autoLoadTotalValue": { "aggregation": "SUM",  "weight": "" },
	"cpuPerRequestTime": { "aggregation": "AVG",  "weight": "" },
	"rowSizeAvg": { "aggregation": "AVG",  "weight": "" },
	"fetchSizeAvg": { "aggregation": "AVG",  "weight": "" },
	"contributionPct": { "aggregation": "AVG",  "weight": "callCount" },
	"callPct": { "aggregation": "AVG",  "weight": "callCount" },
	"callsPerRequest": { "aggregation": "AVG",  "weight": "callCount" },
	"avgCallTime": { "aggregation": "AVG",  "weight": "callCount" },
	"transactionCount": { "aggregation": "SUM",  "weight": "" },
	"failedTransactionCount": { "aggregation": "SUM",  "weight": "" },
	"callCount": { "aggregation": "SUM",  "weight": "" },
	"failedCallCount": { "aggregation": "SUM",  "weight": "" }
}
