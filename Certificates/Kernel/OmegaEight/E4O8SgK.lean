module

public import Certificates.Kernel.OmegaEight.E4O8SgData
public import Certificates.Kernel.OmegaEight.E4O8CentK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E4C

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.KC.PCent CFSG.KC.Misc.ArrEnum CertificateChecks.KernelO8

@[expose] noncomputable def sgS (k : Nat) : Nat :=
  [pid, AP.S 8, pc (AP.S 8) (AP.S 8), AP.S 9, pc (AP.S 9) (AP.S 8),
    pc (AP.S 9) (pc (AP.S 8) (AP.S 8))].getD k pid

@[expose] noncomputable def sgYK (k : Nat) : Nat := sgY.getD k (nat_lit 0)

@[expose] noncomputable def sgQK (i : Nat) : Nat := sgQ.getD i (nat_lit 0)

@[expose] noncomputable def sgUK (i : Nat) : Nat := sgU.getD i (nat_lit 0)

@[expose] noncomputable def sgVK (i : Nat) : Nat := sgV.getD i (nat_lit 0)

@[expose] noncomputable def sgEK (i j : Nat) : Nat := (sgE.getD i []).getD j (nat_lit 0)

@[expose] noncomputable def sgNUK (i j : Nat) : Nat := (sgNU.getD i []).getD j (nat_lit 0)

@[expose] noncomputable def sgNVK (i j : Nat) : Nat := (sgNV.getD i []).getD j (nat_lit 0)

@[expose] def sgInv (j : Nat) : Nat := [0, 1, 3, 2, 5, 4, 7, 6].getD j 0

@[expose] noncomputable def sgClos (L : List Nat) (a b : Nat) : Bool :=
  bAnd(e4Mem L pid, allL (fun x => bAnd(e4Mem L (pc a x), e4Mem L (pc b x))) L)

@[expose] noncomputable def sgIn (i a b : Nat) : Bool :=
  bAnd(e4Mem (sgE.getD i []) a, e4Mem (sgE.getD i []) b)

@[expose] noncomputable def sgCo (a b : Nat) : Bool :=
  bIf(sgIn 0 a b, true, bIf(sgIn 1 a b, true, bIf(sgIn 2 a b, true, sgIn 3 a b)))

@[expose] noncomputable def sgFix (y i : Nat) : Bool := bAnd(e4Comm y (sgUK i), e4Comm y (sgVK i))

@[expose] noncomputable def sgActZ (i zu zv : Nat) : Bool :=
  bIf(allN 8 (fun j => bIf(bAnd(Nat.beq zu (sgNUK i j), Nat.beq zv (sgNVK i j)), false, true)),
    false, true)

@[expose] noncomputable def sgAct (y i : Nat) : Bool :=
  sgActZ i (pc (pc y (sgUK i)) y) (pc (pc y (sgVK i)) y)

@[expose] noncomputable def sgAt (y : Nat) : Bool :=
  bIf(sgFix y 1, true, bIf(sgFix y 2, true, bIf(sgFix y 3, true,
    bIf(sgAct y 1, false, bIf(sgAct y 2, false, bIf(sgAct y 3, false, true))))))

@[expose] noncomputable def sgOne (Y h p : Nat) : Bool :=
  bIf(Nat.blt p 360, bIf(Nat.beq (pg 9 (mask 9) Y (pg 9 (mask 9) h (pg 9 (mask 9) Y
    (pg 9 (mask 9) h p)))) p, false, true), sgAt (pc Y h))

@[expose] noncomputable def sgWalk (Y : Nat) : List (Nat × Nat × Nat × Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun r _ ih ps => bAnd(sgOne Y r.1 (ps.headD (nat_lit 360)), ih ps.tail))

theorem ch55118pm : bAnd(permB 360 9 (AP.S 8), bAnd(permB 360 9 (AP.S 9),
    bAnd(allN 4 (fun i => permB 360 9 (sgUK i)), allN 4 (fun i => permB 360 9 (sgVK i))))) =
      true := by
  quickRfl

theorem ch55118t : bAnd(Nat.beq sgQ.length 3, bAnd(Nat.beq sgQW.length 3, bAnd(e4Lets 6 sgQW,
    bAnd(Nat.beq (sgUK 0) e4U, bAnd(Nat.beq (sgVK 0) om0V,
    allN 3 (fun i => bAnd(Nat.beq (sgQK i) (wordK 360 9 g0K (sgQW.getD i [])),
      bAnd(Nat.beq (pc (sgUK (i + 1)) (sgQK i)) (pc (sgQK i) e4U),
      bAnd(Nat.beq (pc (sgVK (i + 1)) (sgQK i)) (pc (sgQK i) om0V),
        bIf(e4Mem (sgE.getD 0 []) (sgUK (i + 1)), false, true)))))))))) = true := by
  quickRfl

theorem ch55118e : allN 4 (fun i => bAnd(sgE.getD i [] ==
    e4Q (pc (sgUK i) (sgUK i)) (sgUK i) (sgVK i), bAnd(sgClos (sgE.getD i []) (sgUK i) (sgVK i),
    allN 8 (fun j => bAnd(Nat.beq (pc (sgEK i j) (sgEK i (sgInv j))) pid,
      bAnd(Nat.beq (sgNUK i j) (pc (pc (sgEK i j) (sgUK i)) (sgEK i (sgInv j))),
        Nat.beq (sgNVK i j) (pc (pc (sgEK i j) (sgVK i)) (sgEK i (sgInv j))))))))) = true := by
  quickRfl

theorem ch55118r : bAnd(allL (fun a => allL (fun b => bIf(sgCo a b, true, e4Comm a b))
    (RU.map Prod.fst)) (RU.map Prod.fst), bAnd(e4Mem (RU.map Prod.fst) om0V,
    bIf(e4Comm e4U om0V, false, true))) = true := by
  quickRfl

theorem ch55118h : bAnd(orbRecK (fun k y => pcomp 360 9 (mask 9) (g2K k) y) 6 pid sgR,
    Nat.beq sgR.length 1152) = true := by
  quickRfl

theorem ch55118y : bAnd(Nat.beq sgY.length 6, bAnd(Nat.beq sgW.length 6, bAnd(e4Lets 6 sgW,
    allN 6 (fun k => bAnd(Nat.beq (sgYK k) (pc (sgS k) (wordK 360 9 g0K (sgW.getD k []))),
      bAnd(e4Comm (sgYK k) e4U, e4Comm (sgYK k) om0V)))))) = true := by
  quickRfl

theorem ch55118s : allN 6 (fun k => sgWalk (sgYK k) sgR (sgP.getD k [])) = true := by
  quickRfl

end CertificateChecks.KernelO8.E4C

end
