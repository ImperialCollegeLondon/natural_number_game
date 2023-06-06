.PHONY: all
all: html

html: $(shell find src -not -name '*.olean' | sed 's/ /\\ /g')
	$(MAKE) clean
	make-lean-game --devmode
	cp src/game/LaTeX/implies_diag.jpg src/game/LaTeX/function_diag.jpg src/game/LaTeX/FAQ.html html/
	touch html

.PHONY: run
run: html
	echo 'Ctrl+C to stop'
	python3 -m http.server -d html


.PHONY: clean
clean:
	rm -rf html
	rm -rf src/game/**/*.olean
