FROM debian:10-slim as opam

# ------------
#   Get OPAM
# ------------
RUN apt-get update && apt-get install --no-install-recommends -y \
    wget ca-certificates \
    m4 bubblewrap gcc gcc-multilib libc6-dev binutils make patch unzip

# We need to install OPAM 2.0 manually for now.
RUN wget https://github.com/ocaml/opam/releases/download/2.0.6/opam-2.0.6-x86_64-linux -O /usr/bin/opam && chmod 755 /usr/bin/opam

# Basic OPAM setup
ARG NJOBS=2
ENV OPAMJOBS=${NJOBS}          \
    OPAMROOT=/root/.opamcache  \
    OPAMROOTISOK=true

RUN opam init -a --bare --disable-sandboxing

# -----------------
# jsCoq pre-install
# -----------------
RUN opam switch create jscoq+32bit ocaml-variants.4.10.2+32bit

RUN apt install --no-install-recommends -y git rsync bzip2 nodejs curl
RUN curl https://www.npmjs.com/install.sh | sh
# ^ https://github.com/nodejs/help/issues/1877

# ---------------------
# jsCoq toolchain setup
# ---------------------
FROM opam as jscoq-prereq

ARG REPO=https://github.com/jscoq/jscoq

WORKDIR /root
RUN git clone --recursive ${REPO}

WORKDIR jscoq
RUN ./etc/toolchain-setup.sh --32
RUN opam clean -a -c

# -----------
# jsCoq build
# -----------
FROM jscoq-prereq as jscoq

ARG NJOBS=4

RUN git pull
RUN eval $(opam env) && make coq && make jscoq

# - addons
#  (one per RUN, for easy resume)
RUN eval $(opam env) && make addons ADDONS="mathcomp"
RUN eval $(opam env) && opam install -y elpi.1.8.0 && make addons ADDONS="elpi"
RUN eval $(opam env) && make addons ADDONS="equations"
RUN eval $(opam env) && make addons ADDONS="extlib"
RUN eval $(opam env) && make addons ADDONS="simpleio"
RUN eval $(opam env) && make addons ADDONS="quickchick"

# - remake packages after addon build
#   (also creates `*.cma.js`)
RUN eval $(opam env) && rm -rf _build/jscoq+64bit/coq-pkgs \
       && make jscoq ADDONS="mathcomp elpi equations extlib simpleio quickchick"

# - dist tarballs
RUN eval $(opam env) && make dist-tarball && make dist-npm \
        && mkdir dist && mv _build/dist/*.tar.gz dist

# --------------
# Addon packages
# --------------
FROM jscoq as jscoq-addons

# - install to OPAM for use by package builds
RUN eval $(opam env) && make install &&   \
    cd _build/jscoq+* && npm link

ARG ADDONS_REPO=https://github.com/jscoq/addons
ARG ADDONS_BRANCH=v8.12

# - fetch submodules with ssh urls using https instead
#   (to avoid the need for an ssh key)
RUN git config --global url."https://github.com/".insteadOf git@github.com:

WORKDIR /root
RUN git clone --recursive -b ${ADDONS_BRANCH} ${ADDONS_REPO} jscoq-addons

WORKDIR jscoq-addons
RUN make set-ver VER=`jscoq --version`
RUN eval $(opam env) && make

# Private repos: re-enable SSH
COPY /_ssh /_ssh 
RUN [ -e /_ssh/id_rsa ] && rm ~/.gitconfig && apt-get install -y openssh-client
ENV GIT_SSH_COMMAND 'ssh -i /_ssh/id_rsa -o StrictHostKeyChecking=no'

RUN [ -e /_ssh/id_rsa ] && eval $(opam env) && make privates WITH_PRIVATE=software-foundations

RUN make pack

# jsCoq SDK

#RUN cp -rL _build/install/jscoq+64bit/ ./dist && \
#    rm dist/bin/*.byte dist/bin/*.opt \
#       dist/lib/coq/*/*.cmxs \
#       `find dist -regex '.*\.\(cm\(a\|t\|ti\)\|mli?\)'`

#FROM debian:10-slim

#COPY --from=0 /root/jscoq/dist /opt/jscoq

