CP_SYNTAX_FILES=Syntax/AbsCP.hs Syntax/LexCP.x Syntax/PrintCP.hs Syntax/ErrM.hs Syntax/ParCP.y Syntax/SkelCP.hs
CP_SOURCE_FILES=Check.hs Expand.hs CPI.hs Norm.hs
GV_SYNTAX_FILES=Syntax/AbsGV.hs Syntax/LexGV.x Syntax/PrintGV.hs Syntax/ErrM.hs Syntax/ParGV.y Syntax/SkelGV.hs
GV_SOURCE_FILES=CheckGV.hs GVI.hs RunGV.hs CPBuilder.hs ScopeGV.hs
BNFC=~/.cabal/bin/bnfc

all: cpi gvi

cpi: $(CP_SYNTAX_FILES) Syntax/ParCP.hs Syntax/LexCP.hs $(CP_SOURCE_FILES)
	ghc --make -o cpi -O2 -hidir obj -odir obj CPI.hs

$(CP_SYNTAX_FILES): CP.cf
	$(BNFC) -haskell -p Syntax $<
	touch $(CP_SYNTAX_FILES)

Syntax/ParCP.hs: Syntax/ParCP.y
	happy -gca $<

Syntax/LexCP.hs: Syntax/LexCP.x
	alex -g $<

$(GV_SYNTAX_FILES): GV.cf
	$(BNFC) -haskell -p Syntax $<
	touch $(GV_SYNTAX_FILES)

Syntax/ParGV.hs: Syntax/ParGV.y
	happy -gca $<

Syntax/LexGV.hs: Syntax/LexGV.x
	alex -g $<

gvi: $(GV_SYNTAX_FILES) Syntax/ParGV.hs Syntax/LexGV.hs $(GV_SOURCE_FILES) cpi
	ghc --make -o gvi -O2 -hidir obj -odir obj GVI.hs

clean:
	-rm -rf Syntax
	-rm -rf obj
	-rm cpi
	-rm gvi

.PHONY: all clean
