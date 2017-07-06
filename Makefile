UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
  FORMAT=aout
  PIE=
else
ifeq ($(UNAME), Darwin)
  FORMAT=macho
  PIE=
endif
endif

PKGS=oUnit,extlib,unix
BUILD=ocamlbuild -r -use-ocamlfind

main: *.ml parser.mly lexer.mll
	$(BUILD) -no-hygiene -package $(PKGS) main.native
	mv main.native main

test: *.ml parser.mly lexer.mll
	$(BUILD) -no-hygiene -package $(PKGS) test.native
	mv test.native test

testrun: *.ml parser.mly lexer.mll
	$(BUILD) -no-hygiene -package $(PKGS) test.native
	mv test.native test
	./test

output/%.run: output/%.o main.c
	clang $(PIE) -mstackrealign -g -m32 -o $@ main.c $<

output/%.o: output/%.s
	nasm -f $(FORMAT) -o $@ $<

.PRECIOUS: output/%.s
output/%.s: input/%.garter main
	./main $< > $@

# cutest-1.5/CuTest.o: cutest-1.5/CuTest.c cutest-1.5/CuTest.h
# 	gcc -m32 cutest-1.5/CuTest.c -c -g -o cutest-1.5/CuTest.o



clean:
	rm -rf output/*.o output/*.s output/*.dSYM output/*.run *.log *.o
	rm -rf _build/
	rm -f main test
