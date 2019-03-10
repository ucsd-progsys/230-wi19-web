top: AxioMeta

AxioMeta: Axiomatic AxioMeta.hs
	stack exec -- liquid AxioMeta.hs

Verifier: Axiomatic Verifier.hs
	stack exec -- liquid Verifier.hs

Axiomatic: lib Axiomatic.hs 
	stack exec -- liquid Axiomatic.hs 

lib: 
	stack exec -- liquid ProofCombinators.hs 
	stack exec -- liquid State.hs 
	stack exec -- liquid Expressions.hs 
	stack exec -- liquid Imp.hs 
	stack exec -- liquid BigStep.hs 
	# stack exec -- liquid SmallStep.hs 

clean: 
	rm -rf .liquid/*

tags:
	hasktags -x -c . 

