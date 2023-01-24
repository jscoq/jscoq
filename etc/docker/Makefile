.PHONY: default build dist serve clean clean-% wa-% js-%

WHO = jscoq

BRANCH = v8.16

export JSCOQ_REPO = https://github.com/$(WHO)/jscoq.git
export JSCOQ_BRANCH = $(BRANCH)

export NJOBS ?= 4

M := ${shell uname -m}

ifneq (${M},x86_64)
# 32-bit support is only available for x86 processors (esp., not arm64)
export WORDSIZE = 64
endif

# Use BuildKit.
# This is needed for jscoq/wacoq branching in Dockerfile
export DOCKER_BUILDKIT = 1

BUILD_ARGS = BRANCH SUB_BRANCH NJOBS WORDSIZE \
             JSCOQ_REPO JSCOQ_BRANCH

ARGS = $(addprefix --platform , $(firstword ${ARCH})) \
       $(addprefix --build-arg , $(BUILD_ARGS))

-include _config.mk

#uniq = $(if $1,$(firstword $1) $(call uniq,$(filter-out $(firstword $1),$1)))

JS_EXISTING_IMAGES = ${shell docker images --filter=reference="jscoq:*" --format '{{.Repository}}:{{.Tag}}'} ${shell docker images jscoq/jscoq -q}
WA_EXISTING_IMAGES = ${shell docker images --filter=reference="wacoq:*" --format '{{.Repository}}:{{.Tag}}'} ${shell docker images jscoq/wacoq -q}

default: js-build

js-build: js-build-core js-build-addons js-build-sdk

js-build-core:
	docker build . --target jscoq-preinstall $(ARGS)  -t jscoq:preinstall
	docker build . --target jscoq-prereq     $(ARGS)  -t jscoq:prereq
	docker build . --target jscoq            $(ARGS)  -t jscoq

js-build-addons: js-build-core
	docker build . --target jscoq-addons     $(ARGS)  -t jscoq:addons

js-build-inc: js-clean-inc
	docker build . --target jscoq-inc        $(ARGS)  -t jscoq:inc

js-build-sdk: js-build-core
	docker build . --target jscoq-sdk        $(ARGS)  -t jscoq:sdk

wa-build: wa-build-core wa-build-addons

wa-build-core:
	docker build . --target wacoq-preinstall $(ARGS)  -t wacoq:preinstall
	docker build . --target wacoq-prereq     $(ARGS)  -t wacoq:prereq
	docker build . --target wacoq            $(ARGS)  -t wacoq

wa-build-addons: wa-build-core
	docker build . --target wacoq-addons     $(ARGS)  -t wacoq:addons

dist: js-dist wa-dist

clean-dist:
	rm -rf ./dist

js-dist: clean-dist
	docker run --name jscoq-get-dist jscoq:addons \
		sh -c 'mkdir -p dist && cp _build/jscoq+*/*.tgz dist'
	docker cp jscoq-get-dist:/root/jscoq/dist .
	docker cp jscoq-get-dist:/root/jscoq-addons/dist .
	docker rm jscoq-get-dist

wa-dist: clean-dist
	docker run --name wacoq-get-dist wacoq:addons \
		sh -c 'mkdir -p dist && cp _build/wacoq/*.tgz dist'
	docker cp wacoq-get-dist:/root/jscoq+wacoq/dist .
	docker cp wacoq-get-dist:/root/jscoq-addons/dist .
	docker rm wacoq-get-dist

# For getting just the jsCoq package, w/o addons
js-dist-core: clean-dist
	docker run --name jscoq-get-dist jscoq
	docker cp jscoq-get-dist:/root/jscoq/dist .
	docker rm jscoq-get-dist

# For updating the dist with the result of incremental build
js-dist-inc:
	docker run --name jscoq-get-dist jscoq:inc
	docker cp jscoq-get-dist:/root/jscoq/dist .
	docker rm jscoq-get-dist


JS_CLEAN = ${filter-out jscoq:pre%, $(JS_EXISTING_IMAGES)}
WA_CLEAN = ${filter-out wacoq:pre%, $(WA_EXISTING_IMAGES)}

CLEAN_FLAGS = ${if $(JSCOQ_DEV)$(FORCE), -f,}

clean: js-clean wa-clean

js-clean:
	${if $(JS_CLEAN), docker image rm $(CLEAN_FLAGS) $(JS_CLEAN)}
	docker system prune $(CLEAN_FLAGS)   # this seems to be required with BuildKit

wa-clean:
	${if $(WA_CLEAN), docker image rm $(CLEAN_FLAGS) $(WA_CLEAN)}
	docker system prune $(CLEAN_FLAGS)

JS_CLEAN_INC = ${filter jscoq:inc, $(JS_EXISTING_IMAGES)}

js-clean-inc:
	${if $(JS_CLEAN_INC), docker image rm $(CLEAN_FLAGS) $(JS_CLEAN_INC)}
	docker system prune $(CLEAN_FLAGS)

clean-slate: js-clean-slate wa-clean-slate

js-clean-slate:
	${if $(JS_EXISTING_IMAGES), docker image rm $(CLEAN_FLAGS) $(JS_EXISTING_IMAGES)}
	docker system prune $(CLEAN_FLAGS)

wa-clean-slate:
	${if $(WA_EXISTING_IMAGES), docker image rm $(CLEAN_FLAGS) $(WA_EXISTING_IMAGES)}
	docker system prune $(CLEAN_FLAGS)

js-upload:
	docker tag jscoq:sdk jscoq/jscoq:sdk-${M}
	docker push jscoq/jscoq:sdk-${M}

# Update the multi-arch manifest
MANIFEST_ARCHS = x86_64 arm64
js-upload-manifest:
	docker manifest create --amend jscoq/jscoq:sdk \
	       $(addprefix jscoq/jscoq:sdk-, ${MANIFEST_ARCHS})
	docker manifest push jscoq/jscoq:sdk

serve:
	docker run --publish 8080:8080 --rm -it jscoq \
		sh -c "cd _build/dist && npm i && npx -y static-server -p 8080"

dist-serve:
	npx http-server -p 8080 dist

ci:
	make clean && make js-build wa-build && make dist
