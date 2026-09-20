FONTS="./assets/fonts"
.PHONY: format clean

all: main.pdf

%.pdf: %.typ
	@echo "-- building $@ --"
	typst c --ignore-system-fonts --font-path $(FONTS) $< $@

format:
	typstyle --inplace --wrap-text *.typ

clean:
	rm *.pdf
