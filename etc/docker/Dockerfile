FROM debian:10-slim as opam

# ------------
#   Get OPAM
# ------------
RUN dpkg --add-architecture i386 && \
    apt-get update && apt-get install --no-install-recommends -y \
    wget ca-certificates \
    m4 bubblewrap gcc gcc-multilib libc6-dev libgmp-dev:i386 binutils make patch unzip

# We need to install OPAM 2.0 manually for now.
RUN wget https://github.com/ocaml/opam/releases/download/2.0.8/opam-2.0.8-x86_64-linux -O /usr/bin/opam && chmod 755 /usr/bin/opam

# Basic OPAM setup
ARG NJOBS=2
ENV OPAMJOBS=${NJOBS}          \
    OPAMROOT=/root/.opamcache  \
    OPAMROOTISOK=true

RUN opam init -a --bare --disable-sandboxing

# -----------------
# jsCoq pre-install
# -----------------
RUN opam switch create jscoq+32bit --packages="ocaml-variants.4.12.0+options,ocaml-option-32bit"

ENV APT_PACKAGES="git rsync bzip2 nodejs curl libgmp-dev"
RUN apt install --no-install-recommends -y $APT_PACKAGES
RUN curl https://www.npmjs.com/install.sh | sh
# ^ https://github.com/nodejs/help/issues/1877

# ---------------------
# jsCoq toolchain setup
# ---------------------
FROM opam as jscoq-prereq

ARG REPO=https://github.com/jscoq/jscoq
ARG BRANCH=v8.13

WORKDIR /root
RUN git clone --recursive -b ${BRANCH} ${REPO}

WORKDIR jscoq
RUN ./etc/toolchain-setup.sh --32
RUN opam clean -a -c
RUN opam list

# -----------
# jsCoq build
# -----------
FROM jscoq-prereq as jscoq

ARG NJOBS=4

RUN git pull
RUN eval $(opam env) && make coq && make jscoq

# - dist tarballs
RUN eval $(opam env) && make dist-tarball && make dist-npm \
        && mkdir dist && mv _build/dist/*.tar.gz dist

# Addon packages
FROM jscoq as jscoq-addons

# - install to OPAM for use by package builds
RUN eval $(opam env) && make install &&   \
    cd _build/jscoq+* && npm link

ARG ADDONS_REPO=https://github.com/jscoq/addons
ARG ADDONS_BRANCH=v8.13

# - fetch submodules with ssh urls using https instead
#   (to avoid the need for an ssh key)
RUN git config --global url."https://github.com/".insteadOf git@github.com:

WORKDIR /root
RUN git clone --recursive -b ${ADDONS_BRANCH} ${ADDONS_REPO} jscoq-addons

WORKDIR jscoq-addons
RUN make set-ver VER=`jscoq --version`
RUN eval $(opam env) && make

# Private repos: re-enable SSH
COPY Dockerfile _ssh* /root/_ssh/
#    ^ this is a hack in case `_ssh` does not exist (https://stackoverflow.com/a/46801962/37639)
ENV GIT_SSH_COMMAND 'ssh -i /root/_ssh/id_rsa -o StrictHostKeyChecking=no'

RUN if [ -e /root/_ssh/id_rsa ] ; then rm ~/.gitconfig && apt-get install -y openssh-client ; fi
RUN if [ -e /root/_ssh/id_rsa ] ; then eval $(opam env) && make privates WITH_PRIVATE=software-foundations ; fi

RUN make pack

# ---------
# jsCoq SDK
# ---------

FROM jscoq as jscoq-sdk-prepare

RUN cp -rL _build/install/jscoq+*bit/ ./dist-sdk && \
    rm dist-sdk/bin/*.byte dist-sdk/bin/*.opt \
       dist-sdk/lib/coq/*/*.cmxs \
       `find dist -regex '.*\.\(cm\(a\|t\|ti\)\|mli?\)'`

FROM debian:10-slim as jscoq-sdk

COPY --from=jscoq-sdk-prepare /root/jscoq/dist-sdk /opt/jscoq
