FROM debian:10-slim as opam

# ------------
#   Get OPAM
# ------------
RUN dpkg --add-architecture i386 && apt-get update && apt-get upgrade -y apt && \
    apt-get install --no-install-recommends -y \
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

# ----------------------------------------------------------
#
#       j s C o q   (JavaScript backend)
#
# ----------------------------------------------------------

# -----------------
# jsCoq pre-install
# -----------------
FROM opam as jscoq-preinstall

RUN opam switch create jscoq+32bit --packages="ocaml-variants.4.12.0+options,ocaml-option-32bit"

# Other deps: Git, Node.js, GMP
ENV APT_PACKAGES="git rsync bzip2 nodejs curl libgmp-dev"
RUN wget -O- https://deb.nodesource.com/setup_16.x | bash -
# ^ https://github.com/nodesource/distributions/blob/master/README.md
RUN apt install --no-install-recommends -y $APT_PACKAGES

# ---------------------
# jsCoq toolchain setup
# ---------------------
FROM jscoq-preinstall as jscoq-prereq

ARG JSCOQ_REPO=https://github.com/jscoq/jscoq
ARG JSCOQ_BRANCH=v8.14

WORKDIR /root
RUN git clone --recursive -b ${JSCOQ_BRANCH} ${JSCOQ_REPO}

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
        && mkdir dist && mv _build/dist/*.tgz dist

# --------------
# Addon packages
# --------------
FROM jscoq as jscoq-addons

# - install to OPAM for use by package builds
RUN eval $(opam env) && make install &&   \
    cd _build/jscoq+* && npm link

ARG ADDONS_REPO=https://github.com/jscoq/addons
ARG ADDONS_BRANCH=v8.14

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
    rm dist-sdk/bin/*.byte dist-sdk/bin/*.opt

# @todo these have moved; probably some of them are actually needed too.
# rm dist-sdk/lib/coq/*/*.cmxs \
# `find dist-sdk -regex '.*\.\(cm\(a\|t\|ti\)\|mli?\)'`

FROM debian:10-slim as jscoq-sdk

COPY --from=jscoq-sdk-prepare /root/jscoq/dist-sdk /opt/jscoq

COPY sdk-startup.sh /root/sdk-startup.sh

ENTRYPOINT ["/root/sdk-startup.sh"]
ENV PATH /usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/opt/jscoq/bin

# ----------------------------------------------------------
#
#       w a C o q   (WebAssembly backend)
#
# ----------------------------------------------------------

# -----------------
# waCoq pre-install
# -----------------
FROM opam as wacoq-preinstall

RUN opam switch create wacoq --packages="ocaml-base-compiler.4.12.0"

ENV APT_PACKAGES="git rsync bzip2 nodejs curl libgmp-dev"
RUN wget -O- https://deb.nodesource.com/setup_16.x | bash -
# ^ https://github.com/nodesource/distributions/blob/master/README.md
RUN apt-get install --no-install-recommends -y $APT_PACKAGES
#RUN curl https://www.npmjs.com/install.sh | sh
## ^ https://github.com/nodejs/help/issues/1877

ARG WASI_SDK_URL="https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-12/wasi-sdk-12.0-linux.tar.gz"
RUN wget -O/tmp/wasi-sdk.tar.gz ${WASI_SDK_URL}
RUN ( cd /opt && tar xf /tmp/wasi-sdk.tar.gz && ln -s wasi-sdk-* wasi-sdk )

# ---------------------
# waCoq toolchain setup
# ---------------------
FROM wacoq-preinstall as wacoq-prereq

ARG WACOQ_BIN_REPO=https://github.com/jscoq/wacoq-bin.git
ARG WACOQ_BIN_BRANCH=v8.14

WORKDIR /root
RUN git clone --recursive -b ${WACOQ_BIN_BRANCH} ${WACOQ_BIN_REPO} wacoq-bin

WORKDIR wacoq-bin
RUN opam update
RUN ./etc/setup.sh
RUN opam clean -a -c
RUN opam list

# -----------------
# waCoq+jsCoq build
# -----------------
FROM wacoq-prereq as wacoq

ARG JSCOQ_REPO=https://github.com/jscoq/jscoq.git
ARG JSCOQ_BRANCH=v8.14

ARG NJOBS=4

RUN git pull
RUN npm install
RUN eval $(opam env) && make coq && make
RUN make dist-npm

WORKDIR /root
RUN git clone --recursive -b ${JSCOQ_BRANCH} ${JSCOQ_REPO} jscoq+wacoq

WORKDIR jscoq+wacoq
RUN cp ../wacoq-bin/wacoq-bin-*.tar.gz . && npm install ./wacoq-bin-*.tar.gz
RUN npm install
RUN make wacoq
RUN make dist-npm-wacoq

# - dist tarballs
# @oops `dist` is also used by the build...
RUN rm -rf dist && mkdir dist && mv *.tgz ../wacoq-bin/*.tar.gz dist

# --------------
# Addon packages
# --------------
FROM wacoq as wacoq-addons

ARG ADDONS_REPO=https://github.com/jscoq/addons
ARG ADDONS_BRANCH=v8.14

ARG CONTEXT=wacoq

# - install to OPAM for use by package builds
WORKDIR /root/wacoq-bin
RUN eval $(opam env) && make install && npm link

# - fetch submodules with ssh urls using https instead
#   (to avoid the need for an ssh key)
RUN git config --global url."https://github.com/".insteadOf git@github.com:

WORKDIR /root
RUN git clone --recursive -b ${ADDONS_BRANCH} ${ADDONS_REPO} jscoq-addons

WORKDIR jscoq-addons
RUN make set-ver CONTEXT=${CONTEXT}
RUN eval $(opam env) && make CONTEXT=${CONTEXT}

# Private repos: re-enable SSH
COPY Dockerfile _ssh* /root/_ssh/
#    ^ this is a hack in case `_ssh` does not exist (https://stackoverflow.com/a/46801962/37639)
ENV GIT_SSH_COMMAND 'ssh -i /root/_ssh/id_rsa -o StrictHostKeyChecking=no'

RUN if [ -e /root/_ssh/id_rsa ] ; then rm ~/.gitconfig && apt-get update && apt-get install -y openssh-client ; fi
RUN if [ -e /root/_ssh/id_rsa ] ; then eval $(opam env) && make privates WITH_PRIVATE=software-foundations CONTEXT=${CONTEXT} ; fi

RUN make pack CONTEXT=${CONTEXT}
