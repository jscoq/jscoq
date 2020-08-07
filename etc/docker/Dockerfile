FROM debian:10-slim as opam

# ------------
#   Get OPAM
# ------------
RUN apt-get update && apt-get install --no-install-recommends -y \
    wget ca-certificates \
    m4 bubblewrap gcc libc6-dev binutils make patch unzip

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
RUN opam switch create jscoq+64bit ocaml-base-compiler.4.07.1

RUN apt install --no-install-recommends -y git rsync bzip2 nodejs curl
RUN curl https://www.npmjs.com/install.sh | sh
# ^ https://github.com/nodejs/help/issues/1877

# ---------------------
# jsCoq toolchain setup
# ---------------------
FROM opam as jscoq-prereq

ARG REPO=https://github.com/jscoq/jscoq
ARG BRANCH=v8.12

WORKDIR /root
RUN git clone --recursive -b ${BRANCH} ${REPO}

WORKDIR jscoq
RUN ./etc/toolchain-setup.sh --64
RUN opam clean -a -c

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

# - install to OPAM for use by package builds
RUN eval $(opam env) && make install &&   \
    ln -s /root/jscoq/_build/jscoq+64bit/coq-pkgs $OPAM_SWITCH_PREFIX/bin

ARG ADDONS_REPO=https://github.com/jscoq/addons
ARG ADDONS_BRANCH=v8.12

# - allow submodules with ssh urls
RUN git config --global url."https://github.com/".insteadOf git@github.com:

WORKDIR /root
RUN git clone --recursive -b ${ADDONS_BRANCH} ${ADDONS_REPO} jscoq-addons

WORKDIR jscoq-addons
RUN eval $(opam env) && make

RUN make pack

# jsCoq SDK

#RUN cp -rL _build/install/jscoq+64bit/ ./dist && \
#    rm dist/bin/*.byte dist/bin/*.opt \
#       dist/lib/coq/*/*.cmxs \
#       `find dist -regex '.*\.\(cm\(a\|t\|ti\)\|mli?\)'`

#FROM debian:10-slim

#COPY --from=0 /root/jscoq/dist /opt/jscoq

