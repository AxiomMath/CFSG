module

public import Certificates.Kernel.HeLoc.FiveData
public import Certificates.Kernel.SporSch.HeT.Tab
public import Certificates.Data.Kernel.HeLoc.Tree
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.SporSch.PairHeCnt
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CFSG.KC.Misc.Clos (allR)

@[expose] noncomputable def G (k : Nat) : Nat := FH.F (Nat.add 8 k)

@[expose] noncomputable def g (k x : Nat) : Nat := pg 14 (mask 14) (G k) x

@[expose] noncomputable def uF (x : Nat) : Nat := powF (pg 14 (mask 14) (AR.F 0)) 5 x

@[expose] noncomputable def q (k : Nat) : Nat := nIf(Nat.beq k 1, 1, 0)

@[expose] noncomputable def E (i k : Nat) : Nat := fld(C0.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def tv (i x : Nat) : Nat := trV g C0.P C0.L 600 i x

@[expose] def bs : List Nat := [0, 1, 2, 3, 4]

@[expose] noncomputable def key (i : Nat) : Nat :=
  keyV 8330 CFSG.RankThree.PartOne.heFiveKeys (tv i)

@[expose] noncomputable def F (j : Nat) : Nat := NF.getD j 0

@[expose] noncomputable def bindAt (x : Nat) : Bool :=
  bAnd(bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (F 0) (G 0) x,
    bAnd(bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (F 1) (G 2) x,
      Nat.beq (g 1 (uF x)) (HeTc.nfp (F 2) x)))

@[expose] noncomputable def bindB (c : Nat) : Bool := allR (Nat.mul 833 c) 833 bindAt

@[expose] noncomputable def fourAt (i : Nat) : Bool :=
  bIf(eqOnL bs (powF (tv i) 4) (fun x => x),
    bIf(eqOnL bs (powF (tv i) 2) (fun x => x), true, Nat.beq (trQ q C0.P C0.L 600 i) 1), true)

theorem kPerm : CFSG.KC.Enum.allN 3 (fun k => permOK 8330 14 (mask 14) (8330 * 14) (G k) (FI k)) = true := by
  quickRfl

theorem kNF : CFSG.KC.Enum.allN 3 (fun j => nfValidK 5 HeC.LR (F j)) = true := by quickRfl

theorem kB0 : bindB 0 = true := by quickRfl
theorem kB1 : bindB 1 = true := by quickRfl
theorem kB2 : bindB 2 = true := by quickRfl
theorem kB3 : bindB 3 = true := by quickRfl
theorem kB4 : bindB 4 = true := by quickRfl
theorem kB5 : bindB 5 = true := by quickRfl
theorem kB6 : bindB 6 = true := by quickRfl
theorem kB7 : bindB 7 = true := by quickRfl
theorem kB8 : bindB 8 = true := by quickRfl
theorem kB9 : bindB 9 = true := by quickRfl

theorem kN : Nat.beq C0.N 600 = true := by quickRfl

theorem kTree : CFSG.KC.Enum.allN 600 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 C0.P C0.L i)) = true := by
  quickRfl

theorem kReplay : CFSG.KC.Bfs.replayOK E 3 600 = true := by quickRfl

theorem kEdge : CFSG.KC.Enum.allN 600 (edgeAtK g q C0.P C0.L E 600 600 3 bs) = true := by
  quickRfl

theorem kSort : CFSG.KC.Enum.allN 600 (sortAtK key C0.SK C0.SKI 600) = true := by quickRfl

theorem kFour : CFSG.KC.Enum.allN 600 fourAt = true := by quickRfl

end CertificateChecks.KernelHeLoc.Five

end
