# Base branch, used for addons
ARG BASE_BRANCH=v8.20
# jsCoq branch, to be overriden for example in PRs
ARG BRANCH=v8.20

ARG WORDSIZE=32
ARG SWITCH=jscoq+${WORDSIZE}bit

FROM debian:11-slim AS coq-base

# -------------------------------------------- #
# Setup WASI, OPAM, and Coq's System build env #
# -------------------------------------------- #

ARG NJOBS=2
ARG WORDSIZE
ARG WASI_SDK_URL="https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-12/wasi-sdk-12.0-linux.tar.gz"

RUN if [ ${WORDSIZE} = 32 ] ; then dpkg --add-architecture i386 ; fi

RUN apt-get update -qq && apt-get upgrade -y -qq apt && \
    apt-get install --no-install-recommends -y -qq \
    wget curl rsync git bzip2 ca-certificates \
    m4 bubblewrap gcc libc6-dev binutils make patch unzip \
    opam libgmp-dev pkg-config

RUN if [ ${WORDSIZE} = 32 ] ; then \
    apt install --no-install-recommends -y -qq gcc-multilib libgmp-dev:i386; fi

# Updated node, cannot be before due to lack of wget
RUN wget -O- https://deb.nodesource.com/setup_22.x | bash -
RUN apt-get update -qq && apt-get install --no-install-recommends -y -qq nodejs

# wasi-sdk (for waCoq)
# ^ https://github.com/nodesource/distributions/blob/master/README.md
RUN wget --quiet -O/tmp/wasi-sdk.tar.gz ${WASI_SDK_URL}
RUN ( cd /opt && tar xf /tmp/wasi-sdk.tar.gz && ln -s wasi-sdk-* wasi-sdk )

# Basic OPAM setup
ENV OPAMJOBS=${NJOBS}          \
    OPAMROOT=/root/.opamcache  \
    OPAMROOTISOK=true

RUN opam init -a --bare --disable-sandboxing

RUN apt-get clean

# ----------------------------------------------------------
#
#       j s C o q   (JavaScript and WebAssembly backend)
#
# ----------------------------------------------------------

# ------------------------------------------ #
# jsCoq OCaml-level dependencies pre-install #
# ------------------------------------------ #
FROM coq-base AS jscoq-base

ARG SWITCH
ARG WORDSIZE
ARG BRANCH

RUN if [ ${WORDSIZE} != 32 ] ; then opam switch create ${SWITCH} 4.14.2 ; fi
RUN if [ ${WORDSIZE} = 32 ] ;  then opam switch create ${SWITCH} --packages="ocaml-variants.4.14.2+options,ocaml-option-32bit" ; fi

ARG JSCOQ_REPO=https://github.com/jscoq/jscoq
ARG JSCOQ_BRANCH=${BRANCH}

WORKDIR /root
RUN git clone --recursive -b ${JSCOQ_BRANCH} ${JSCOQ_REPO}

WORKDIR jscoq
RUN ./etc/toolchain-setup.sh --${WORDSIZE}
RUN opam clean -a -c
RUN opam list

# -----------
# jsCoq build
# -----------
FROM jscoq-base AS jscoq

ARG SUB_BRANCH
ARG NJOBS=4

RUN git pull --ff-only
RUN if [ _${SUB_BRANCH} != _ ] ; then git checkout ${SUB_BRANCH} && git pull --ff-only ; fi
RUN eval $(opam env) && make coq
RUN export JSCOQ_BUNDLE_TARGET=release
RUN eval $(opam env) && make jscoq
RUN eval $(opam env) && make wacoq

# - dist tarballs
RUN eval $(opam env) && make dist && make dist-npm \
        && mkdir -p dist && mv _build/dist/*.tgz dist

# --------------
# Addon packages
# --------------
FROM jscoq AS jscoq-addons

# - install to OPAM for use by package builds
RUN eval $(opam env) && make install &&   \
    cd _build/jscoq+* && npm link

ARG BASE_BRANCH
ARG BRANCH
ARG WORDSIZE
ARG SWITCH
ARG ADDONS_REPO=https://github.com/jscoq/addons
ARG ADDONS_BRANCH=${BASE_BRANCH}

# - fetch submodules with ssh urls using https instead
#   (to avoid the need for an ssh key)
RUN git config --global url."https://github.com/".insteadOf git@github.com:

WORKDIR /root
RUN git clone --recursive -b ${ADDONS_BRANCH} ${ADDONS_REPO} jscoq-addons

WORKDIR jscoq-addons
RUN make set-ver VER=`jscoq --version`
RUN eval $(opam env) && git pull && git submodule update && make CONTEXT=${SWITCH}

# Private repos: re-enable SSH
COPY Dockerfile _ssh* /root/_ssh/
#    ^ this is a hack in case `_ssh` does not exist (https://stackoverflow.com/a/46801962/37639)
ENV GIT_SSH_COMMAND 'ssh -i /root/_ssh/id_rsa -o StrictHostKeyChecking=no'

RUN if [ -e /root/_ssh/id_rsa ] ; then rm ~/.gitconfig && apt-get install -y openssh-client ; fi
RUN if [ -e /root/_ssh/id_rsa ] ; then eval $(opam env) && make privates WITH_PRIVATE=software-foundations ; fi

RUN make pack CONTEXT=${SWITCH}

# -------------------------
# Building small increments
# -------------------------

FROM jscoq-addons AS jscoq-inc

ARG SUB_BRANCH
ARG NJOBS=4

WORKDIR /root/jscoq
RUN git pull --ff-only
RUN if [ _${SUB_BRANCH} != _ ] ; then git checkout ${SUB_BRANCH} && git pull --ff-only ; fi
RUN eval $(opam env) && make jscoq

# - dist tarballs
RUN eval $(opam env) && make dist-tarball && make dist-npm \
        && mkdir -p dist && mv _build/dist/*.tgz dist

# ---------
# jsCoq SDK
# ---------

FROM jscoq AS jscoq-sdk-prepare

RUN cp -rL _build/install/jscoq+*bit/ ./dist-sdk && \
    rm dist-sdk/bin/*.byte dist-sdk/bin/*.opt

# @todo these have moved; probably some of them are actually needed too.
# rm dist-sdk/lib/coq/*/*.cmxs \
# `find dist-sdk -regex '.*\.\(cm\(a\|t\|ti\)\|mli?\)'`

FROM debian:11-slim AS jscoq-sdk

ARG WORDSIZE

COPY --from=jscoq-sdk-prepare /root/jscoq/dist-sdk /opt/jscoq

# Needs to be squashed into a single step to facilitate cleanup
RUN if [ ${WORDSIZE} = 32 ] ; then \
        dpkg --add-architecture i386 && apt-get update && \
        apt-get install --no-install-recommends -y \
            libgmp10:i386 libc6-i386 ; \
    else apt-get update ; \
    fi ; \
    apt-get install --no-install-recommends -y gosu sudo && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

COPY gosu-entrypoint.sh /root/gosu-entrypoint.sh
COPY sdk-findlib.conf /opt/jscoq/findlib.conf
ENTRYPOINT ["/root/gosu-entrypoint.sh"]

ENV PATH /usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/opt/jscoq/bin
ENV OCAMLFIND_CONF /opt/jscoq/findlib.conf
