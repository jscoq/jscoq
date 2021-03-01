.PHONY: build dist serve

WHO = jscoq

export REPO = https://github.com/$(WHO)/jscoq
export NJOBS ?= 4

ARGS = --build-arg REPO --build-arg NJOBS

build:
	docker build . --target opam         $(ARGS)  -t opam
	docker build . --target jscoq-prereq $(ARGS)  -t jscoq:prereq
	docker build . --target jscoq        $(ARGS)  -t jscoq

dist:
	rm -rf ./dist
	docker run --name jscoq-get-dist jscoq:addons \
		sh -c 'mkdir -p dist && cp _build/jscoq+*/*.tgz dist'
	docker cp jscoq-get-dist:/root/jscoq/dist .
	docker rm jscoq-get-dist

serve:
	docker run --publish 8080:8080 --rm -it jscoq \
		npx static-server -p 8080 _build/dist
