#!/bin/bash

rm -f test_summary.log
failedTests=0
for d in */ ; do
    pushd "$d"
    testName=`basename "$d"`
    echo "Test: $testName"
    ./run_tests.sh
    if [ ! -f "test_summary.log" ]; then
        echo "$testName FAILED ❌: $testname/test_summary.log file not generated."
        failedTests=`expr $failedTests + 1`
    fi
    if ! cmp -s test_summary.log expected_summary.log
    then
      echo "$testName FAILED ❌: Integration test output different to expected. See $testName/test_summary.log and $testName/expected_summary.log" 1>> ../test_summary.log
      echo "If the expected summary is out of date, alter $testName/expected_summary.log."
      failedTests=`expr $failedTests + 1`
    else
      echo "$testName PASSED ✅" 1>> ../test_summary.log
    fi
    popd > /dev/null
done

echo "-----INTEGRATION-TESTS-SUMMARY------"
cat test_summary.log
echo "------------------------------------"

if [ $failedTests -eq 0 ]; then
  echo "All integration tests passed ✅"
else
  echo "$failedTests test(s) FAILED ❌"
  exit 1
fi