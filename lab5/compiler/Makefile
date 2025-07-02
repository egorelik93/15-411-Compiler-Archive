all: l4c

l4c:
	runhaskell Setup.hs configure --user
	runhaskell Setup.hs build
	rm -rf bin/
	cp -r shellbins/ bin/
	chmod +x bin/*
prof:
	rm -rf ../../cabal-dev-sandbox/bin
	cabal-dev install --sandbox=../../cabal-dev-sandbox --cabal-install-arg='--enable-library-profiling' --cabal-install-arg='--enable-executable-profiling' --ghc-options='-auto-all' --ghc-options='-prof'
	rm -rf bin/
	cp -r shellbins/ bin/
	chmod +x bin/*
clean:
	rm -rf bin/
	rm -rf dist/
