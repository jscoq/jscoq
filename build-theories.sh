
COQVER=v8.10
COQDIR=coq-external/coq-$COQVER
COQBUILDDIR=_build/default/$COQDIR

here=`pwd`

# These files interfere with the build somehow
find $COQDIR/doc/plugin_tutorial -name dune -exec rm {} \;
rm -f $COQDIR/ide/dune

# Generate dune files for theories
dune build $COQDIR/.vfiles.d $COQDIR/tools/coq_dune.exe
( cd $COQDIR && $here/$COQBUILDDIR/tools/coq_dune.exe $here/$COQBUILDDIR/.vfiles.d )

# Run Coq build again
dune build $COQDIR

