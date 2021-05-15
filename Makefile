.PHONY: all clean force
.PHONY: dist dist-npm app

all:
	npm run build

clean:
	rm -f wacoq-*.tar.gz ui-js/*.browser.js* ui-js/addon/*.browser.js* 
	rm -rf ui-js/*-images ui-js/addon/*-images

########################################################################
# Dists                                                                #
########################################################################

BUILDOBJ =  \
	ui-js ui-css ui-images examples \
	node_modules ui-external/CodeMirror-TeX-input
DISTOBJ = README.md index.html package.json package-lock.json $(BUILDOBJ)
DISTDIR = _build/dist

PACKAGE_VERSION = ${shell node -p 'require("./package.json").version'}

dist:
	mkdir -p $(DISTDIR)
	rsync -apR --delete $(DISTOBJ) $(DISTDIR)

TAREXCLUDE = --exclude node_modules --exclude '*.cma' \
    ${foreach dir, Coq Ltac2 mathcomp, \
		--exclude '${dir}/**/*.vo' --exclude '${dir}/**/*.cma.js'}

dist-tarball: dist
	# Hack to make the tar contain a wacoq-x.x directory
	@rm -f _build/wacoq-$(PACKAGE_VERSION)
	ln -fs dist _build/wacoq-$(PACKAGE_VERSION)
	tar zcf /tmp/wacoq-$(PACKAGE_VERSION).tar.gz   \
	    -C _build $(TAREXCLUDE) --exclude '*.bak' --exclude '*.tar.gz' \
	    --dereference wacoq-$(PACKAGE_VERSION)
	mv /tmp/wacoq-$(PACKAGE_VERSION).tar.gz $(DISTDIR)
	@rm -f _build/wacoq-$(PACKAGE_VERSION)

NPMOBJ = ${filter-out node_modules index.html, $(DISTOBJ)}
NPMSTAGEDIR = _build/package
NPMEXCLUDE = --delete-excluded --exclude '*.cma' --exclude app \
    ${foreach dir, Coq Ltac2 mathcomp, \
		--exclude '${dir}/**/*.vo' --exclude '${dir}/**/*.cma.js'}

dist-npm:
	mkdir -p $(NPMSTAGEDIR) $(DISTDIR)
	rsync -apR --delete $(NPMEXCLUDE) $(NPMOBJ) $(NPMSTAGEDIR)
	cp docs/npm-landing.html $(NPMSTAGEDIR)/index.html
	npm pack ./$(NPMSTAGEDIR)

# Electron app bundle (macOS)

APPOBJ = ${filter-out node_modules package%.json, $(DISTOBJ)}
APPSTAGEDIR = _build/app
APPDMGDIR = $(APPSTAGEDIR)/dmg/Vin.app

app: ui-images/app/icon.icns
	mkdir -p $(APPSTAGEDIR)/Contents/Resources/app
	rsync -apRL --delete `cat ui-js/app/external.list` \
	    --delete-excluded ${foreach m, assets '*.map', --exclude $m} \
		$(APPOBJ) $(APPSTAGEDIR)/Contents/Resources/app/
	cp ui-js/app/package.json $(APPSTAGEDIR)/Contents/Resources/app/

app-dmg:
	mkdir -p $(APPDMGDIR)
	rsync -apR --delete /opt/local/lib/node_modules/electron/dist/Electron.app/./ \
	   $(APPSTAGEDIR)/./Contents/Resources/app \
	   $(APPDMGDIR)
	cp ui-js/app/Info.plist $(APPDMGDIR)/Contents/
	cp ui-images/app/icon.icns $(APPDMGDIR)/Contents/Resources/vin.icns
	hdiutil create -volname Vin -srcfolder $(APPSTAGEDIR)/dmg -ov -format UDZO Vin.dmg

%.icns: %.png
	ui-images/app/png-to-icns $< $*

server:
	npx http-server . -p 8013
