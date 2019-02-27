top: SmallStep

Verifier: Floyd Verifier.hs
	stack exec -- liquid Verifier.hs

Floyd: BigStep FloydHoare.hs 
	stack exec -- liquid FloydHoare.hs 

SmallStep: BigStep SmallStep.hs 
	stack exec -- liquid SmallStep.hs 

BigStep: Imp BigStep.hs 
	stack exec -- liquid BigStep.hs 

Imp: Expressions Imp.hs
	stack exec -- liquid Imp.hs 

Expressions: State Expressions.hs
	stack exec -- liquid Expressions.hs 

State: ProofCombinators State.hs
	stack exec -- liquid State.hs 

ProofCombinators: ProofCombinators.hs 
	stack exec -- liquid ProofCombinators.hs 

clean: 
	rm -rf .liquid/*

tags:
	hasktags -x -c . 

