# Directory where the coq sources are
COQDIR=~/external/coq-git/

# Addons to build
ADDONS =
# ADDONS += ssr-libs mtac coquelicot flocq tlc color sf cpdt hott dsp relalg unimath plugin-utils cel mirror-core

# Have in every add-on a make jscoq target? We could certainly
# classify coq_makefile ones.
ADDONS_PATH=/home/egallego/external/coq

# Custom stdlib for hott
HOTT_COQLIB=/home/egallego/external/HoTT/coq/theories/

RELEASE_DIR=~/research/jscoq-builds/
WEB_DIR=~/x80/rhino-coq/
HOTT_RELEASE=~/x80/rhino-hott/
