SUBMIT := backend.ml team.txt

HWNAME := hw03
ZIPNAME := $(HWNAME)-submit.zip

all: main.native

.PHONY: test
test: main.native
	./main.native --test

test-full: main.native
	./main.native --full-test

main.native: $(SUBMIT)
	ocamlbuild -Is util,x86,ll,grading,sharedtests -libs unix,str main.native -use-menhir

main.byte: $(SUBMIT)
	ocamlbuild -Is util,x86,ll,grading,sharedtests -libs unix,str main.byte -use-menhir

.PHONY: utop repl
utop: main.byte
	utop -require unix,str

repl: utop

zip: $(SUBMIT)
	zip '$(ZIPNAME)' $(SUBMIT)

.PHONY: clean
clean:
	ocamlbuild -clean
	rm -rf output a.out
