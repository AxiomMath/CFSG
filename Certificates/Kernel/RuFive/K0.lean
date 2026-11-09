module

public import Certificates.Kernel.RuFive.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.AllChunks
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Data.Kernel.HeLoc.PTail
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Kernel.RuFive.Tab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc

theorem kCTree : allN 1000 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 C0.P C0.L i)) = true := by
  quickRfl

theorem kCReplay : CFSG.KC.Bfs.replayOK CE 3 1000 = true := by quickRfl

theorem kCEdge : allN 1000 (edgeAtK gC q0 C0.P C0.L CE 1000 1000 3 bs) = true := by quickRfl

theorem kCSort : allN 1000 (sortAtK ckey C0.SK C0.SKI 1000) = true := by quickRfl

theorem kATree : allN 125 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 A0.P A0.L i)) = true := by
  quickRfl

theorem kAReplay : CFSG.KC.Bfs.replayOK AE 3 125 = true := by quickRfl

theorem kAEdge : allN 125 (edgeAtK gA q0 A0.P A0.L AE 125 125 3 bs) = true := by quickRfl

theorem kASort : allN 125 (sortAtK akey A0.SK A0.SKI 125) = true := by quickRfl

theorem kRels0 : CFSG.RankThree.PartOne.ruCase0Rels.all relAt0 = true := by quickRfl

theorem kComm0 : allN 3 (fun k => eqOnL bs (fun y => gC k (x0 y)) (fun y => x0 (gC k y))) = true := by
  quickRfl

theorem kEq0 : Nat.beq (F 64) (F 2) = true := by quickRfl

theorem kFR0 : allN 9 (fun i => bIf(Nat.beq (fr0 i) 0, true,
    bAnd(Nat.blt (Nat.div (Nat.sub (fr0 i) 1) 8) i, bAnd(Nat.blt (Nat.mod (Nat.sub (fr0 i) 1) 8) 5,
      CFSG.RankThree.PartOne.ruCase0Rels.any fun r =>
        bAnd(Nat.beq r.1 (Nat.div (Nat.sub (fr0 i) 1) 8), bAnd(Nat.beq r.2.1 i,
          Nat.beq r.2.2 (Nat.mod (Nat.sub (fr0 i) 1) 8))))))) = true := by
  quickRfl

theorem kAinC : allN 3 (fun l => bAnd(Nat.blt (AW.getD l 0) 1000,
    eqOnL bs (cv (AW.getD l 0)) (gA l))) = true := by
  quickRfl

theorem kConj : allN 9 (fun m => bAnd(Nat.blt (CW.getD m 0) 125,
    eqOnL bs (av (CW.getD m 0)) (fun y => gC (Nat.div m 3) (gA (Nat.mod m 3)
      (pi (Nat.add 64 (Nat.div m 3)) y))))) = true := by
  quickRfl

theorem kAPow : allN 125 (fun i => eqOnL bs (powF (av i) 5) (fun y => y)) = true := by quickRfl

theorem kXinA : bAnd(Nat.blt (XW.getD 0 0) 125, eqOnL bs (av (XW.getD 0 0)) x0) = true := by
  quickRfl

theorem kZ0 : allN 1000 zAt0 = true := by quickRfl

theorem strictB_eqK (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem ptK_succ_zR (n w kS NR NL : Nat) (LT PT QT LR FR : Nat → Nat)
    (rels : List (Nat × Nat × Nat)) (xm : Nat → Nat) (cb ps : List Nat) (KE SK : Nat → Nat)
    (NE m i : Nat) (acc accI img : Nat → Nat) (h : FR i = 0) :
    ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE (m + 1) i acc accI img =
      allN (rcnt (LR i)) fun k => strictB (acc (rpt w (mask w) (LR i) k)) fun p =>
        bIf(relK rels xm (imgExt img i p) i,
          ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE m (Nat.succ i)
            (fun y => acc (trPtT w NR NL LT PT i k y))
            (fun y => trInvPtT w kS NR NL LT PT i k (accI y)) (imgExt img i p), true) := by
  show strictB (rcnt (LR i)) (fun c => strictB (FR i) fun fr => bIf(Nat.beq fr 0,
    allN c fun k => strictB (acc (rpt w (mask w) (LR i) k)) fun p =>
      bIf(relK rels xm (imgExt img i p) i,
        ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE m (Nat.succ i)
          (fun y => acc (trPtT w NR NL LT PT i k y))
          (fun y => trInvPtT w kS NR NL LT PT i k (accI y)) (imgExt img i p), true),
    strictB (accI (powF xm (Nat.mod (Nat.sub fr 1) 8) (img (Nat.div (Nat.sub fr 1) 8))))
      fun q => strictB (lvT NL w QT i q) fun k =>
      bIf(Nat.blt k c, strictB (acc (rpt w (mask w) (LR i) k)) fun p =>
        bIf(relK rels xm (imgExt img i p) i,
          ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE m (Nat.succ i)
            (fun y => acc (trPtT w NR NL LT PT i k y))
            (fun y => trInvPtT w kS NR NL LT PT i k (accI y)) (imgExt img i p), true),
        true))) = _
  rw [strictB_eqK, strictB_eqK, h]
  rfl

theorem fr0_zero : fr0 0 = 0 := Nat.eq_of_beq_eq_true (by quickRfl)

set_option maxHeartbeats 0 in
theorem kTail0_0 : (((List.range (rcnt (S50.LR 0))).drop (0 * 508)).take 508).all
    (fun k => strictB (rpt 12 (mask 12) (S50.LR 0) k) fun p =>
      bIf(relK CFSG.RankThree.PartOne.ruCase0Rels x0 (imgExt (fun _ => 0) 0 p) 0,
        ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
      CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK 1000 8 (Nat.succ 0)
          (fun y => trPtT 12 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (fun y => trInvPtT 12 8 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (imgExt (fun _ => 0) 0 p), true)) = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kTail0_1 : (((List.range (rcnt (S50.LR 0))).drop (1 * 508)).take 508).all
    (fun k => strictB (rpt 12 (mask 12) (S50.LR 0) k) fun p =>
      bIf(relK CFSG.RankThree.PartOne.ruCase0Rels x0 (imgExt (fun _ => 0) 0 p) 0,
        ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
      CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK 1000 8 (Nat.succ 0)
          (fun y => trPtT 12 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (fun y => trInvPtT 12 8 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (imgExt (fun _ => 0) 0 p), true)) = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kTail0_2 : (((List.range (rcnt (S50.LR 0))).drop (2 * 508)).take 508).all
    (fun k => strictB (rpt 12 (mask 12) (S50.LR 0) k) fun p =>
      bIf(relK CFSG.RankThree.PartOne.ruCase0Rels x0 (imgExt (fun _ => 0) 0 p) 0,
        ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
      CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK 1000 8 (Nat.succ 0)
          (fun y => trPtT 12 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (fun y => trInvPtT 12 8 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (imgExt (fun _ => 0) 0 p), true)) = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kTail0_3 : (((List.range (rcnt (S50.LR 0))).drop (3 * 508)).take 508).all
    (fun k => strictB (rpt 12 (mask 12) (S50.LR 0) k) fun p =>
      bIf(relK CFSG.RankThree.PartOne.ruCase0Rels x0 (imgExt (fun _ => 0) 0 p) 0,
        ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
      CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK 1000 8 (Nat.succ 0)
          (fun y => trPtT 12 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (fun y => trInvPtT 12 8 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (imgExt (fun _ => 0) 0 p), true)) = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kTail0_4 : (((List.range (rcnt (S50.LR 0))).drop (4 * 508)).take 508).all
    (fun k => strictB (rpt 12 (mask 12) (S50.LR 0) k) fun p =>
      bIf(relK CFSG.RankThree.PartOne.ruCase0Rels x0 (imgExt (fun _ => 0) 0 p) 0,
        ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
      CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK 1000 8 (Nat.succ 0)
          (fun y => trPtT 12 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (fun y => trInvPtT 12 8 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (imgExt (fun _ => 0) 0 p), true)) = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kTail0_5 : (((List.range (rcnt (S50.LR 0))).drop (5 * 508)).take 508).all
    (fun k => strictB (rpt 12 (mask 12) (S50.LR 0) k) fun p =>
      bIf(relK CFSG.RankThree.PartOne.ruCase0Rels x0 (imgExt (fun _ => 0) 0 p) 0,
        ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
      CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK 1000 8 (Nat.succ 0)
          (fun y => trPtT 12 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (fun y => trInvPtT 12 8 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (imgExt (fun _ => 0) 0 p), true)) = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kTail0_6 : (((List.range (rcnt (S50.LR 0))).drop (6 * 508)).take 508).all
    (fun k => strictB (rpt 12 (mask 12) (S50.LR 0) k) fun p =>
      bIf(relK CFSG.RankThree.PartOne.ruCase0Rels x0 (imgExt (fun _ => 0) 0 p) 0,
        ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
      CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK 1000 8 (Nat.succ 0)
          (fun y => trPtT 12 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (fun y => trInvPtT 12 8 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (imgExt (fun _ => 0) 0 p), true)) = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kTail0_7 : (((List.range (rcnt (S50.LR 0))).drop (7 * 508)).take 508).all
    (fun k => strictB (rpt 12 (mask 12) (S50.LR 0) k) fun p =>
      bIf(relK CFSG.RankThree.PartOne.ruCase0Rels x0 (imgExt (fun _ => 0) 0 p) 0,
        ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
      CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK 1000 8 (Nat.succ 0)
          (fun y => trPtT 12 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (fun y => trInvPtT 12 8 T50.NR T50.NR T50.LT T50.PT 0 k y)
          (imgExt (fun _ => 0) 0 p), true)) = true := by
  quickRfl

theorem kTail0 : ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
    CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK
    1000 9 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by
  rw [show (9 : Nat) = 8 + 1 from rfl, ptK_succ_zR (h := fr0_zero), CFSG.KS.Raw.Orb.allN_eq]
  refine CFSG.KC.AllChunks.all_of_chunks _ _ 508 8 (by rw [List.length_range]; decide +kernel) ?_
  intro k hk
  match k, hk with
  | 0, _ => exact kTail0_0
  | 1, _ => exact kTail0_1
  | 2, _ => exact kTail0_2
  | 3, _ => exact kTail0_3
  | 4, _ => exact kTail0_4
  | 5, _ => exact kTail0_5
  | 6, _ => exact kTail0_6
  | 7, _ => exact kTail0_7
  | k + 8, h => exact absurd h (by omega)

end CertificateChecks.KernelRuFive

end
