#Formal Verification of System FC in Coq

Haskell's compiler, the Glasgow Haskell Compiler (GHC), generates code in GHC Core. The Coq proof assistant will be used to verify a formalized version of System FC, the basis for GHC Core. A translation from the formal language to GHC Core, the concrete implementation of System FC that is used in GHC, will then be proven. The goals of verification are to prove that the evaluation semantics of System FC are sound.

There are two main benefits to this project. First, the verification would provide assurance regarding the safety and accuracy of GHC. Second, and perhaps more importantly, it will provide foundation to verify other properties of GHC such as compiler optimizations.

##Contents:
* `proposal/` LaTeX source for the project proposal
* `coq/` Coq source code for the formalization and proofs of the System FC type system