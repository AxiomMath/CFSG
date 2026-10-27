module

public import Certificates.Kernel.HNDce2.Data
public import Certificates.Data.Kernel.TwistDce2.Rels
public import CFSG.Sporadic.Recognition.HNMultiplierInputs

public section

namespace CFSG.KD.HNDce2

open CFSG.KC.TwDce2 CFSG.Sporadic.Recognition.HNMultiplier

@[expose] def invCodes (w : List ℕ) : List ℕ := (w.map fun c => Nat.xor c 1).reverse

@[expose] def commCodes (c : List (List ℕ × List ℕ)) : List ℕ :=
  (c.map fun p => p.1 ++ p.2 ++ invCodes p.1 ++ invCodes p.2).flatten

@[expose] def hnXCodes : List (List ℕ) :=
  ([0, 1, 2, 3, 4] : List (Fin 7)).map fun i => (2 * i.val + 1) :: commCodes (hnCommCodes i)

@[expose] def hnRCodes : List (List ℕ) :=
  hnRelCodes1 ++ [hnGDefCodes] ++ hnRelCodes2 ++ hnNCodes ++ hnXCodes

theorem rels_ok : relsOK F 1408 hnRCodes = true := by
  decide +kernel

theorem node1_ok :
    CFSG.KC.TwDce.andB (fixesPt F INVM RW (CFSG.KC.LaneChain.getL CG 1) 0) (invCodesOK INVM 6) =
      true := by
  decide +kernel

end CFSG.KD.HNDce2

end
