module

public import Certificates.Kernel.RouteP.Data.Y332
public import CFSG.Sporadic.Recognition.Fi22MultiplierInputs

public section

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP CFSG.YGroups CFSG.Sporadic.Recognition.Fi22Multiplier

@[expose] def yReg (j : Nat) : Nat := if j < 9 then 33 + 2 * j else j + 41

@[expose] def yWs : List (List Nat) := yRels 3 3 2 ++ [f332Word]

@[expose] def yw (i : Nat) : List Int := (yWs[i]!).map fun c => -((yReg c + 1 : Nat) : Int)

@[expose] noncomputable def yck (g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (idKOK NWY KAY KBY (yw (Nat.div g 20)))
    (idOK NWY (yw (Nat.div g 20)) (Nat.mod g 20)) (Nat.blt (Nat.mod g 20) 19)

@[expose] noncomputable def yfix (g : Nat) : Bool :=
  (fun x => ptOK NWY KAY KBY [((yReg (Nat.div g 2) + 1 : Nat) : Int)] x x)
    (nIf(Nat.beq (Nat.mod g 2) 0, 0, 1479))

@[expose] def yStarts : List Nat := [0, 9, 19, 29, 39, 49, 59, 69, 71]

@[expose] def yBase : List Nat := [15, 18, 27, 30, 3, 6, 9, 12]

@[expose] def ySizes : List Nat := [28160, 3159, 288, 7, 12, 5, 4, 3]

@[expose] def yRounds : List Nat := [33, 5, 3, 1, 2, 1, 1, 1]

@[expose] def yLevel (j : Nat) : Nat := ((yStarts.drop 1).filter (· ≤ j)).length

@[expose] noncomputable def ybase (j : Nat) : Bool :=
  (fun x => ptOK NWY KAY KBY [((yReg j + 1 : Nat) : Int)] x x) (yBase[yLevel j - 1]!)

@[expose] def yLetters (i : Nat) : List Int :=
  (List.range (yStarts[i + 1]! - yStarts[i]!)).flatMap fun t =>
    [-((yReg (yStarts[i]! + t) + 1 : Nat) : Int), ((yReg (yStarts[i]! + t) + 1 : Nat) : Int)]

@[expose] noncomputable def ylev (i : Nat) : Bool :=
  orbOK NWY KAY KBY (yLetters i) (yBase[i]!) (yRounds[i]!) (ySizes[i]!)

@[expose] noncomputable def nkY (j : Nat) : Bool :=
  andB (CFSG.KC.Fi24Net.netOK (NWY j)) (kapOK KAY KBY j)

end CFSG.KD.RouteP

end
