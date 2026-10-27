module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl

public section

namespace CertificateChecks.KernelWeylHyp

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native CFSG.Blueprint.Chevalley
  Timmesfeld.Co1Leaf

@[expose] def famAt (τ : Tag) (fl : List Nat) : Bool :=
  famOK (gramL τ) (rootsN τ) (simpleL τ) ((simpleL τ).map fun e => formB (gramL τ) e e)
    (kerBasis 3 fl)

@[expose] def sliceOK (τ : Tag) (k : Nat) : Bool :=
  (((normVecs 3 τ.rank).drop (40 * k)).take 40).all (famAt τ)

@[expose] def e7S (j s : Nat) : Bool := sliceOK .E7 (10 * j + s)

@[expose] def e8S (j s : Nat) : Bool := sliceOK .E8 (10 * j + s)

end CertificateChecks.KernelWeylHyp

end
