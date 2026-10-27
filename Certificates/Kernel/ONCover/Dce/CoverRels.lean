module

public import Certificates.Kernel.ONCover.Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover
public import CFSG.Sporadic.Recognition.ONMultiplierInputs

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce3 CFSG.Sporadic.Recognition.ONMultiplier

@[expose] def dceCode (x : ℕ) : ℕ := 2 * [0, 2, 1].getD (x / 2) 0 + x % 2

@[expose] def invCodes (w : List ℕ) : List ℕ := (w.map fun c => Nat.xor c 1).reverse

@[expose] def commCodes (c : List (List ℕ × List ℕ)) : List ℕ :=
  (c.map fun p => p.1 ++ p.2 ++ invCodes p.1 ++ invCodes p.2).flatten

@[expose] def onHCodes : List (List ℕ) :=
  ((onRelCodes.filter fun w => w.all (· / 2 < 3)) ++
    ([0, 1, 2] : List (Fin 4)).map (fun i => (2 * i.val + 1) :: commCodes (onCommCodes i))).map
      (List.map dceCode) ++ [[6], [7], [8], [9], [10], [11]]

set_option maxRecDepth 100000 in
theorem rels_ok : relsOK 14 FO 11172 onHCodes = true := by
  decide +kernel

end CFSG.KD.ONCoverDce3

end
