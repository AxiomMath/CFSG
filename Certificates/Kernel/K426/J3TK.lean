module

public import Certificates.Kernel.K426.J3TData
public import Certificates.Kernel.SporSch.J3K426.Text
public import Certificates.Kernel.SporSch.PairJ3.ClData
public import Certificates.Data.Kernel.HeLoc.Tree
public import Certificates.Data.Kernel.HeLoc.PTail
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK426J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CertificateChecks.KernelSporSch CFSG.RankThree.PartTwo.KFacts.K426

@[expose] noncomputable def F (k : Nat) : Nat := J3KT.F k

@[expose] noncomputable def g (k x : Nat) : Nat := pg 13 (mask 13) (F k) x

@[expose] noncomputable def gi (k x : Nat) : Nat := pg 13 (mask 13) (FI k) x

@[expose] def bs : List Nat := [0, 1, 3, 2]

@[expose] def q0 (_ : Nat) : Nat := 0

@[expose] noncomputable def gq (k x : Nat) : Nat := g k x

@[expose] noncomputable def ga (k x : Nat) : Nat := g (Nat.add 33 k) x

@[expose] noncomputable def gd (k x : Nat) : Nat := g (Nat.add 37 k) x

@[expose] noncomputable def EQ (i k : Nat) : Nat := fld(TQ.ER i, Nat.mul 16 k, 65535)
@[expose] noncomputable def EA (i k : Nat) : Nat := fld(TA.ER i, Nat.mul 16 k, 65535)
@[expose] noncomputable def ED (i k : Nat) : Nat := fld(TD.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def tq (i x : Nat) : Nat := trV gq TQ.P TQ.L 243 i x
@[expose] noncomputable def ta (i x : Nat) : Nat := trV ga TA.P TA.L 1080 i x
@[expose] noncomputable def td (i x : Nat) : Nat := trV gd TD.P TD.L 360 i x

@[expose] noncomputable def kq (i : Nat) : Nat := keyV 6156 j3tKeys (tq i)
@[expose] noncomputable def ka (i : Nat) : Nat := keyV 6156 j3tKeys (ta i)
@[expose] noncomputable def kd (i : Nat) : Nat := keyV 6156 j3tKeys (td i)

@[expose] noncomputable def lineAt (k : Nat) : Bool :=
  bIf(eqOnL bs (powF (tq k) 3) (fun x => x),
    bIf(eqOnL bs (tq k) (fun x => x), true,
      CFSG.KC.LQT.P.anyN 13 fun j => CFSG.KC.LQT.P.anyN 3 fun e =>
        eqOnL bs (tq k) (powF (g (Nat.add 5 j)) e)), true)

@[expose] noncomputable def wvD (w : List (Fin 2 × Bool)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun a _ ih x => Bool.rec (motive := fun _ => Nat) (gi (Nat.add 37 a.1.val) (ih x))
      (g (Nat.add 37 a.1.val) (ih x)) a.2) w

@[expose] noncomputable def uF (x : Nat) : Nat := wvD j3tWu x
@[expose] noncomputable def vF (x : Nat) : Nat := wvD j3tWv x

@[expose] noncomputable def relAt (y : Nat) (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt r.2.2 3, bAnd(Nat.blt r.1 4, bAnd(Nat.blt r.2.1 4,
    Nat.beq (powF (g y) r.2.2 (bs.getD r.1 0)) (bs.getD r.2.1 0))))

@[expose] noncomputable def fr (i : Nat) : Nat := nIf(Nat.beq i 1, 2, nIf(Nat.beq i 2, 10, 0))

theorem kPerm : allN 40 (fun k => permOK 6156 13 (mask 13) (6156 * 13) (F k) (FI k)) = true := by
  quickRfl

theorem kW0 : allN 10 (fun k => wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5
    (WS.getD k []) (F k)) = true := by quickRfl

theorem kW1 : allN 10 (fun k => wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5
    (WS.getD (Nat.add 10 k) []) (F (Nat.add 10 k))) = true := by quickRfl

theorem kW2 : allN 10 (fun k => wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5
    (WS.getD (Nat.add 20 k) []) (F (Nat.add 20 k))) = true := by quickRfl

theorem kW3 : allN 10 (fun k => wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5
    (WS.getD (Nat.add 30 k) []) (F (Nat.add 30 k))) = true := by quickRfl

theorem kNQ : Nat.beq TQ.N 243 = true := by quickRfl

theorem kNA : Nat.beq TA.N 1080 = true := by quickRfl

theorem kND : Nat.beq TD.N 360 = true := by quickRfl

theorem kTreeQ : allN 243 (fun i => bIf(Nat.beq i 0, true, treeAtK 5 TQ.P TQ.L i)) = true := by
  quickRfl

theorem kTreeA : allN 1080 (fun i => bIf(Nat.beq i 0, true, treeAtK 4 TA.P TA.L i)) = true := by
  quickRfl

theorem kTreeD : allN 360 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 TD.P TD.L i)) = true := by
  quickRfl

theorem kReplayQ : CFSG.KC.Bfs.replayOK EQ 5 243 = true := by quickRfl

theorem kReplayA : CFSG.KC.Bfs.replayOK EA 4 1080 = true := by quickRfl

theorem kReplayD : CFSG.KC.Bfs.replayOK ED 2 360 = true := by quickRfl

theorem kEdgeQ : allN 243 (edgeAtK gq q0 TQ.P TQ.L EQ 243 243 5 bs) = true := by quickRfl

theorem kEdgeA : allN 1080 (edgeAtK ga q0 TA.P TA.L EA 1080 1080 4 bs) = true := by quickRfl

theorem kEdgeD : allN 360 (edgeAtK gd q0 TD.P TD.L ED 360 360 2 bs) = true := by quickRfl

theorem kSortQ : allN 243 (sortAtK kq TQ.SK TQ.SKI 243) = true := by quickRfl

theorem kSortA : allN 1080 (sortAtK ka TA.SK TA.SKI 1080) = true := by quickRfl

theorem kSortD : allN 360 (sortAtK kd TD.SK TD.SKI 360) = true := by quickRfl

theorem kLines : allN 243 lineAt = true := by quickRfl

theorem kCubes : allN 13 (fun j => eqOnL bs (powF (g (Nat.add 5 j)) 3) (fun x => x)) = true ∧
    allN 2 (fun c => eqOnL bs (powF (g (Nat.add 18 c)) 3) (fun x => x)) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem kTrans : allN 13 (fun j => eqOnL bs
    (fun x => g (Nat.add 20 j) (g (Nat.add 18 (j3tRec.getD j 0)) (gi (Nat.add 20 j) x)))
    (g (Nat.add 5 j))) = true := by quickRfl

theorem kRels : j3tRelsA.all (relAt 18) = true ∧ j3tRelsB.all (relAt 19) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem kComm : allN 4 (fun k => eqOnL bs (fun x => ga k (g 18 x)) (fun x => g 18 (ga k x))) =
    true ∧ allN 5 (fun k => eqOnL bs (fun x => gq k (g 19 x)) (fun x => g 19 (gq k x))) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem kDW : allN 8 (fun m => bAnd(Nat.blt (DW.getD m 0) 360, eqOnL bs (td (DW.getD m 0))
      (fun x => ga (Nat.div m 2) (gd (Nat.mod m 2) (gi (Nat.add 33 (Nat.div m 2)) x))))) = true ∧
    allN 16 (fun m => bAnd(Nat.blt (DW.getD (Nat.add 8 m) 0) 360,
      eqOnL bs (td (DW.getD (Nat.add 8 m) 0)) (fun x => ga (Nat.div m 4) (ga (Nat.mod m 4)
        (gi (Nat.add 33 (Nat.div m 4)) (gi (Nat.add 33 (Nat.mod m 4)) x)))))) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem kRelD : j3tA6Rels.all (fun w => eqOnL bs (wvD w) (fun x => x)) = true := by quickRfl

theorem kDet : bAnd(eqOnL bs (fun x => g 39 (uF (gi 39 x))) vF,
    bAnd(eqOnL bs (fun x => g 39 (vF (gi 39 x))) (fun x => uF (powF vF 1 x)),
      eqOnL bs (fun x => uF (vF x)) (fun x => vF (uF x)))) = true := by quickRfl

theorem kTailA : ptK 6156 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3T.QT PJ3.LR fr j3tRelsA (g 18)
    bs j3tKeys ka TA.SK 1080 4 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by quickRfl

theorem kTailB : ptK 6156 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3T.QT PJ3.LR fr j3tRelsB (g 19)
    bs j3tKeys kq TQ.SK 243 4 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by quickRfl

end CertificateChecks.KernelK426J3

end
