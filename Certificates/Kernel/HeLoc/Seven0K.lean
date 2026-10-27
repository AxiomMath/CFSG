module

public import Certificates.Kernel.HeLoc.Seven0Data
public import Certificates.Kernel.HeLoc.Seven0Tab
public import Certificates.Kernel.HeLoc.SevenDefs
public import Certificates.Data.Kernel.HeLoc.PTail
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def gC (k x : Nat) : Nat := pa (Nat.add 59 k) x

@[expose] noncomputable def gA (k x : Nat) : Nat := pa (Nat.add 62 k) x

@[expose] noncomputable def qC (k : Nat) : Nat := FL.getD (Nat.add 59 k) 0

@[expose] noncomputable def CE (i k : Nat) : Nat := fld(C0.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def AE (i k : Nat) : Nat := fld(A0.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def cv (i x : Nat) : Nat := trV gC C0.P C0.L 2058 i x

@[expose] noncomputable def av (i x : Nat) : Nat := trV gA A0.P A0.L 343 i x

@[expose] noncomputable def ckey (i : Nat) : Nat := keyV 8330 CFSG.RankThree.PartOne.heSevenKeys (cv i)

@[expose] noncomputable def akey (i : Nat) : Nat := keyV 8330 CFSG.RankThree.PartOne.heSevenKeys (av i)

@[expose] noncomputable def cq (i : Nat) : Nat := trQ qC C0.P C0.L 2058 i

@[expose] noncomputable def x0 (y : Nat) : Nat := ln 0 y

@[expose] noncomputable def relAt (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt r.2.2 7, bAnd(Nat.blt r.1 14, bAnd(Nat.blt r.2.1 14,
    Nat.beq (powF x0 r.2.2 (CFSG.RankThree.PartOne.heSevenCase0BaseArr[r.1]!))
      (CFSG.RankThree.PartOne.heSevenCase0BaseArr[r.2.1]!))))

@[expose] noncomputable def zAt (c : Nat) : Bool :=
  strictB (ZW0.getD c 0) fun w => bIf(Nat.blt w 100,
    bAnd(Nat.blt 0 w, bAnd(Nat.blt w 4,
      !eqOnL bs (fun y => cv c (gA (Nat.sub w 1) y)) (fun y => gA (Nat.sub w 1) (cv c y)))),
    bAnd(Nat.blt (Nat.sub w 100) 7, bAnd(Nat.beq (cq c) 0,
      eqOnL bs (cv c) (powF x0 (Nat.sub w 100)))))

@[expose] noncomputable def fr0 (i : Nat) : Nat := FR0.getD i 0

theorem kCTree : allN 2058 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 C0.P C0.L i)) = true := by
  quickRfl

theorem kCReplay : CFSG.KC.Bfs.replayOK CE 3 2058 = true := by quickRfl

theorem kCEdge : allN 2058 (edgeAtK gC qC C0.P C0.L CE 2058 2058 3 bs) = true := by quickRfl

theorem kCSort : allN 2058 (sortAtK ckey C0.SK C0.SKI 2058) = true := by quickRfl

theorem kATree : allN 343 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 A0.P A0.L i)) = true := by
  quickRfl

theorem kAReplay : CFSG.KC.Bfs.replayOK AE 3 343 = true := by quickRfl

theorem kAEdge : allN 343 (edgeAtK gA q0 A0.P A0.L AE 343 343 3 bs) = true := by quickRfl

theorem kASort : allN 343 (sortAtK akey A0.SK A0.SKI 343) = true := by quickRfl

theorem kRels : CFSG.RankThree.PartOne.heSevenCase0Rels.all relAt = true := by quickRfl

theorem kComm : allN 3 (fun k => eqOnL bs (fun y => gC k (x0 y)) (fun y => x0 (gC k y))) = true := by
  quickRfl

theorem kAinC : allN 3 (fun l => bAnd(Nat.blt (AW0.getD l 0) 2058,
    bAnd(Nat.beq (cq (AW0.getD l 0)) 0, eqOnL bs (cv (AW0.getD l 0)) (gA l)))) = true := by
  quickRfl

theorem kConj : allN 9 (fun m => bAnd(Nat.blt (CW0.getD m 0) 343,
    eqOnL bs (av (CW0.getD m 0)) (fun y => gC (Nat.div m 3) (gA (Nat.mod m 3)
      (pi (Nat.add 59 (Nat.div m 3)) y))))) = true := by
  quickRfl

theorem kAPow : allN 343 (fun i => eqOnL bs (powF (av i) 7) (fun y => y)) = true := by quickRfl

theorem kXinA : bAnd(Nat.blt (XW0.getD 0 0) 343, eqOnL bs (av (XW0.getD 0 0)) x0) = true := by
  quickRfl

theorem kZ : allN 2058 zAt = true := by
  have key : ∀ (L : List Nat) (n : Nat) (g : Nat → Nat → Bool), L.length = n →
      (List.range n).all (fun c => g c (L.getD c 0)) = L.zipIdx.all (fun p => g p.2 p.1) := by
    intro L n g hn
    subst hn
    have e : L.zipIdx = (List.range L.length).map (fun c => (L.getD c 0, c)) := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range, Nat.zero_add]
      rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    rw [e, List.all_map]
    rfl
  have hs : ZW0.length = 2058 := by rfl
  have h2 : ZW0.zipIdx.all (fun p => strictB p.1 fun w => bIf(Nat.blt w 100,
      bAnd(Nat.blt 0 w, bAnd(Nat.blt w 4,
        !eqOnL bs (fun y => cv p.2 (gA (Nat.sub w 1) y)) (fun y => gA (Nat.sub w 1) (cv p.2 y)))),
      bAnd(Nat.blt (Nat.sub w 100) 7, bAnd(Nat.beq (cq p.2) 0,
        eqOnL bs (cv p.2) (powF x0 (Nat.sub w 100)))))) = true := by
    quickRfl
  have h3 := (key ZW0 2058 (fun c v => strictB v fun w => bIf(Nat.blt w 100,
      bAnd(Nat.blt 0 w, bAnd(Nat.blt w 4,
        !eqOnL bs (fun y => cv c (gA (Nat.sub w 1) y)) (fun y => gA (Nat.sub w 1) (cv c y)))),
      bAnd(Nat.blt (Nat.sub w 100) 7, bAnd(Nat.beq (cq c) 0,
        eqOnL bs (cv c) (powF x0 (Nat.sub w 100)))))) hs).trans h2
  rw [CFSG.KS.PK.allN_eq]
  exact h3

theorem kFR : allN 14 (fun i => bIf(Nat.beq (fr0 i) 0, true,
    bAnd(Nat.blt (Nat.div (Nat.sub (fr0 i) 1) 8) i, bAnd(Nat.blt (Nat.mod (Nat.sub (fr0 i) 1) 8) 7,
      CFSG.RankThree.PartOne.heSevenCase0Rels.any fun r =>
        bAnd(Nat.beq r.1 (Nat.div (Nat.sub (fr0 i) 1) 8), bAnd(Nat.beq r.2.1 i,
          Nat.beq r.2.2 (Nat.mod (Nat.sub (fr0 i) 1) 8))))))) = true := by
  quickRfl

theorem kTail : ptK 8330 14 10 T70.NR T70.NR T70.LT T70.PT T70.QT S70.LR fr0
    CFSG.RankThree.PartOne.heSevenCase0Rels x0 bs CFSG.RankThree.PartOne.heSevenKeys ckey C0.SK
    2058 14 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by
  quickRfl

end CertificateChecks.KernelHeLoc.Seven

end
