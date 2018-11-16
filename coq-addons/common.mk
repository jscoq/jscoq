# -*- mode: makefile -*-

SYNC=rsync -avq
SYNCVO=echo "Updating $<" && rsync -avq --filter='+ */' --filter='+ **.vo' --filter='- *' --prune-empty-dirs
