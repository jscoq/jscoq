
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

# Frugal Coq install
for d in _build/*/$COQDIR; do
    mkdir -p $d/bin 
    rm -f $d/bin/coqtop       ; ln -sf ../topbin/coqtop_bin.exe     $d/bin/coqtop
    rm -f $d/bin/coqc         ; ln -sf ../topbin/coqc_bin.exe       $d/bin/coqc
    rm -f $d/bin/coqdep       ; ln -sf ../tools/coqdep.exe          $d/bin/coqdep
    rm -f $d/bin/coq_makefile ; ln -sf ../tools/coq_makefile.exe    $d/bin/coq_makefile
done
