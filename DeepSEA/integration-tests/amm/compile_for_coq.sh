# TODO - improve and standardise between integration tests

# Arg 1 - takes the file to be compiled (full path). If not supplied, the .ds file to be compiled should be in the current directory (and the only .ds file in the directory).
# Note, coqc must be on the path (if using opam, eval $(opam env) may need to be run, or possibly added to this script along with a relevant opam switch ...)

set -e

if [ -z "$1" ]
then
    FILEBASENAME="`ls *.ds`" # Assume compile-for-coq is called from the directory containing the contract.ds file (and only one such file). May want to remove this if having multiple contracts in this repo.
else
    FILEBASENAME=`basename $1`
    cd `dirname $1`
fi

FILENAMENOEXT="${FILEBASENAME%.*}"
FILEEXT="${FILEBASENAME##*.}"



if [ "$FILEEXT" != "ds" ]
then
    echo -e "ERROR: File needs to be a .ds file."
    echo "-----SUMMARY------"
    cat test_summary.log
    exit 1
fi

rm -rf "$FILENAMENOEXT" # You may want to remove this line if you do not wish the folder to be deleted on every run of `compile-for-coq` e.g. if filling in some proofs within the auto-generated files.
../../_build/default/Edsger/edsger.bc "$FILEBASENAME" coq
cd "$FILENAMENOEXT"

coqdep -f _CoqProject > .coqdeps.d
coq_makefile -arg "-quiet" -f _CoqProject -o core.make 

make -f core.make

# You may want to remove the line below if you are using a custom _CoqProject or have multiple contracts within the repository.
echo "-R ../.. DeepSpec
-R . SmartContract
-R $FILENAMENOEXT $FILENAMENOEXT
FunctionalCorrectness.v
" > ../_CoqProject # Generates a relevant _CoqProject at the root, from the dsc generated _CoqProject   

cd ..