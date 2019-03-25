# -*- mode: makefile -*-

SYNC=rsync -avq
SYNCVO=rsync -avq --filter='+ */' --filter='+ **.vo' --filter='- *' --prune-empty-dirs
