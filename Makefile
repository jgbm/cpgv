SYNTAX_FILES=Syntax/AbsCP.hs Syntax/LexCP.x Syntax/PrintCP.hs Syntax/ErrM.hs Syntax/ParCP.y Syntax/SkelCP.hs
SOURCE_FILES=Check.hs Expand.hs Main.hs Norm.hs
BNFC=~/.cabal/bin/bnfc

all: $(SYNTAX_FILES) Syntax/ParCP.hs Syntax/LexCP.hs $(SOURCE_FILES)
	ghc --make -o cpi -O2 -hidir obj -odir obj Main.hs

$(SYNTAX_FILES): CP.cf
	$(BNFC) -haskell -p Syntax $<

Syntax/ParCP.hs: Syntax/ParCP.y
	happy -gca $<

Syntax/LexCP.hs: Syntax/LexCP.x
	alex -g $<

clean:
	-rm -rf Syntax
	-rm -rf obj
	-rm cpi

.PHONY: all clean