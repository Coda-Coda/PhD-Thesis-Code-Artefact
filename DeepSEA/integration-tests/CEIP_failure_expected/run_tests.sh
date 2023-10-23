# TODO - improve and standardise between integration tests

rm -f test_summary.log
rm -f FunctionalCorrectness.vo
rm -f FunctionalCorrectness.glob

# List of .ds files which should fail to compile
toTest=("CEIP_failure_expected1AB.ds" "CEIP_failure_expected1A.ds" "CEIP_failure_expected1BC.ds" "CEIP_failure_expected1B.ds" "CEIP_failure_expected1CA.ds" "CEIP_failure_expected1C.ds" "CEIP_failure_expected2A.ds" "CEIP_failure_expected2B.ds" "CEIP_failure_expected2C.ds" "CEIP_failure_expected3.ds" "CEIP_failure_expected4.ds")

# Compile to Coq Test
echo "🛈  Compiling to Coq: dsc ... coq" 1>> test_summary.log

errorCount=0
for f in ${toTest[@]}; do
    ./compile_for_coq.sh $f; compilationExitCode=$?  
    if [ $compilationExitCode -eq 0 ]; then
        echo " Compilation of $f Succeeded - This is unexpected - ❌ Test FAILED" 1>> test_summary.log
        ((errorCount+=1))
    else
        echo " Compilation of $f Failed - This is expected - ✅ Test Passed" 1>> test_summary.log
    fi
done

echo "-----SUMMARY------"
cat test_summary.log    

if [ $errorCount -ne 0 ]; then
    exit 1
fi