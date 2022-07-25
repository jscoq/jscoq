
MARKDOWN = python -m markdown -x extra

default: welcome.html

%.html: %.md res/header.in.html res/footer.in.html
	( cat res/header.in.html && $(MARKDOWN) $*.md && \
	  cat res/footer.in.html ) > $@