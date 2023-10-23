# TODO - improve and standardise between integration tests

rm -f test_summary.log
rm -f FunctionalCorrectness.vo
rm -f FunctionalCorrectness.glob

# Compile to Coq Test
echo "🛈  Compiling to Coq: dsc ... coq" 1>> test_summary.log
./compile_for_coq.sh; compilationExitCode=$?
if [ $compilationExitCode -eq 0 ]; then
    echo " ✅ Test Passed" 1>> test_summary.log
else
    echo " ❌ Test FAILED" 1>> test_summary.log
    echo "-----SUMMARY------"
    cat test_summary.log
    exit 1
fi

# Compile Functional Correcteness Test
coqdep -f _CoqProject > .coqdeps.d
coq_makefile -arg "-quiet" -f _CoqProject -o core.make 
echo "🛈  FunctionalCorrectness.v Compilation Test" 1>> test_summary.log
make -f core.make; FCcompilationExitCode=$?
if [ $FCcompilationExitCode -eq 0 ]; then
    echo " ✅ Test Passed" 1>> test_summary.log
else
    echo " ❌ Test FAILED" 1>> test_summary.log
    echo "-----SUMMARY------"
    cat test_summary.log
    exit 1
fi

# No top-level axioms test
rm -f axioms.log
rm -f coqchk/FunctionalCorrectness.vo
mkdir -p coqchk
cp FunctionalCorrectness.vo coqchk/FunctionalCorrectness.vo
cd coqchk
coqchk -silent -o -norec SmartContract.FunctionalCorrectness -R ../../.. DeepSpec -R ../checks_effections_interaction_pattern checks_effections_interaction_pattern -R . SmartContract 2> ../axioms.log
cd ..
AXIOM_FILTER_STRING='    SmartContract.'
NUMBER_OF_AXIOMS_AT_TOP_LEVEL=$(cat axioms.log | grep -c "$AXIOM_FILTER_STRING")
echo "🛈  FunctionalCorrectness.v Top Level Axioms Test" 1>> test_summary.log
if [ $NUMBER_OF_AXIOMS_AT_TOP_LEVEL == "0" ]; then
        echo " ✅ Test Passed (no axioms at the top level)" 1>> test_summary.log
    else
        echo " ❌ Test FAILED ($NUMBER_OF_AXIOMS_AT_TOP_LEVEL axiom(s) at the top level present):" 1>> test_summary.log
        less axioms.log | grep "$AXIOM_FILTER_STRING"  1>> test_summary.log
        echo "-----SUMMARY------"
        cat test_summary.log
        exit 1
fi

echo "-----SUMMARY------"
cat test_summary.log