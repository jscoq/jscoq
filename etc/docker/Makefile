.PHONY: build dist serve

WHO = jscoq

export WACOQ_BIN_REPO = https://github.com/corwin-of-amber/wacoq-bin.git
export WACOQ_BIN_BRANCH = v8.13

export JSCOQ_REPO = https://github.com/$(WHO)/jscoq.git
export JSCOQ_BRANCH = v8.13+wacoq

export NJOBS ?= 4
ARGS = --build-arg WACOQ_BIN_REPO --build-arg WACOQ_BIN_BRANCH \
	   --build-arg JSCOQ_REPO --build-arg JSCOQ_BRANCH --build-arg NJOBS
# --progress plain --no-cache=true

-include _config.mk

EXISTING_IMAGES = ${shell docker images --filter=reference="wacoq:*" --format '{{.Repository}}:{{.Tag}}'}

build:
	docker build . --target opam         $(ARGS)  -t wacoq:opam
	docker build . --target wacoq-prereq $(ARGS)  -t wacoq:prereq
	docker build . --target wacoq        $(ARGS)  -t wacoq
	docker build . --target wacoq-addons $(ARGS)  -t wacoq:addons
#	docker build . --target wacoq-sdk    $(ARGS)  -t wacoq:sdk

dist:
	rm -rf ./dist
	docker run --name wacoq-get-dist wacoq:addons \
		sh -c 'mkdir -p dist && cp _build/wacoq/*.tgz dist'
	docker cp wacoq-get-dist:/root/jscoq+wacoq/dist .
	docker cp wacoq-get-dist:/root/jscoq-addons/dist .
	docker rm wacoq-get-dist

clean:
	docker image rm ${filter-out jscoq:opam jscoq:prereq, $(EXISTING_IMAGES)}

clean-slate:
	docker image rm $(EXISTING_IMAGES)

serve:
	docker run --publish 8080:8080 --rm -it jscoq \
		npx static-server -p 8080 _build/dist

dist-serve:
	npx http-server -p 8080 dist

ci:
	make clean && make && make dist
