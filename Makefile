HS_SOURCES = CP/Check.hs CP/Expand.hs CP/Lexer.hs CP/Norm.hs CP/Parser.hs CP/Printer.hs CP/Syntax.hs CPI.hs GV/Check.hs GV/CPBuilder.hs GV/Lexer.hs GV/Parser.hs GV/Run.hs GV/Scope.hs GV/Syntax.hs GVI.hs

all: cpi gvi

%.hs: %.x
	alex $<

%.hs: %.y
	happy $<

cpi: $(HS_SOURCES)
	ghc --make -o cpi -O2 -hidir obj -odir obj CPI.hs

gvi: $(HS_SOURCES)
	ghc --make -o gvi -O2 -hidir obj -odir obj GVI.hs

clean:
	-rm -rf obj
	-rm cpi
	-rm gvi

.PHONY: all clean
