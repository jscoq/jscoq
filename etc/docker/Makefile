.PHONY: build dist serve clean clean-% wa-% js-%

WHO = jscoq

export JSCOQ_REPO = https://github.com/$(WHO)/jscoq.git
export JSCOQ_BRANCH = v8.13

export WACOQ_BIN_REPO = https://github.com/$(WHO)/wacoq-bin.git
export WACOQ_BIN_BRANCH = v8.13

export NJOBS ?= 4

# Use BuildKit.
# This is needed for jscoq/wacoq branching in Dockerfile
export DOCKER_BUILDKIT = 1

ARGS = --build-arg JSCOQ_REPO --build-arg JSCOQ_BRANCH \
	   --build-arg WACOQ_BIN_REPO --build-arg WACOQ_BIN_BRANCH \
	   --build-arg NJOBS

-include _config.mk

JS_EXISTING_IMAGES = ${shell docker images --filter=reference="jscoq:*" --format '{{.Repository}}:{{.Tag}}'}
WA_EXISTING_IMAGES = ${shell docker images --filter=reference="wacoq:*" --format '{{.Repository}}:{{.Tag}}'}

js-build:
	docker build . --target jscoq-preinstall $(ARGS)  -t jscoq:preinstall
	docker build . --target jscoq-prereq     $(ARGS)  -t jscoq:prereq
	docker build . --target jscoq            $(ARGS)  -t jscoq
	docker build . --target jscoq-addons     $(ARGS)  -t jscoq:addons

wa-build:
	docker build . --target wacoq-preinstall $(ARGS)  -t wacoq:preinstall
	docker build . --target wacoq-prereq     $(ARGS)  -t wacoq:prereq
	docker build . --target wacoq            $(ARGS)  -t wacoq
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

JS_CLEAN = ${filter-out jscoq:pre%, $(JS_EXISTING_IMAGES)}
WA_CLEAN = ${filter-out wacoq:pre%, $(WA_EXISTING_IMAGES)}

clean: js-clean wa-clean

js-clean:
	${if $(JS_CLEAN), docker image rm $(JS_CLEAN)}
	docker system prune -f   # this seems to be required with BuildKit

wa-clean:
	${if $(WA_CLEAN), docker image rm $(WA_CLEAN)}
	docker system prune -f

clean-slate: js-clean-slate wa-clean-slate

js-clean-slate:
	${if $(JS_EXISTING_IMAGES), docker image rm $(JS_EXISTING_IMAGES)}
	docker system prune -f

wa-clean-slate:
	${if $(WA_EXISTING_IMAGES), docker image rm $(WA_EXISTING_IMAGES)}
	docker system prune -f

serve:
	docker run --publish 8080:8080 --rm -it jscoq \
		npx static-server -p 8080 _build/dist

dist-serve:
	npx http-server -p 8080 dist

ci:
	make clean && make js-build wa-build && make dist
