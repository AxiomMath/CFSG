module

public import Certificates.Kernel.Sporadic.OddCore.HN2090K
public import Certificates.Kernel.SporSch.HN.Strong
public import CFSG.Certificates.Kernel.SporSch.HNF5RankKronSound
public import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2090

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNSchreier CFSG.ONSchreier.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HNStrong CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CertificateChecks.KernelSpor

theorem ok (k : Nat) (hk : k < 90) : KrOK HNI.MT HNI.OP HNI.L HNI.R k := by
  rcases (by omega : k < 35 ∨ (35 ≤ k ∧ k < 44) ∨ (44 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 63) ∨
      (63 ≤ k ∧ k < 77) ∨ 77 ≤ k) with h | h | h | h | h | h
  · exact krOK_of_blk blk0 (by omega) (by omega)
  · exact krOK_of_blk blk1 (by omega) (by omega)
  · exact krOK_of_blk blk2 (by omega) (by omega)
  · exact krOK_of_blk blk3 (by omega) (by omega)
  · exact krOK_of_blk blk4 (by omega) (by omega)
  · exact krOK_of_blk blk5 (by omega) (by omega)

theorem canon (k : Nat) (hk : k < 90) : Canon5 (sr k) := (ok k hk).1

theorem mul_eq {K l r : Nat} (hl1 : l < 90) (hr1 : r < 90) (hK : K < 90) (ho : HNI.OP K = 0)
    (hl : HNI.L K = l) (hr : HNI.R K = r) :
    mulM 5 133 (rows5 (sr l)) (rows5 (sr r)) = rows5 (sr K) :=
  krOK_mul (ok K hK) (canon l hl1) (canon r hr1) ho hl hr

@[expose] def ltR (l : Int) : Nat := if 0 < l then l.toNat - 1 else 16 + (-l).toNat

theorem mletter_R {l : Int} (h0 : l ≠ 0) (h17 : l.natAbs ≤ 17) :
    mletter SA SIA l = rows5 (sr (ltR l)) := by
  rw [mletter_eq h0 h17, letK, ltR]
  by_cases hp : 0 < l
  · simp only [hp, ↓reduceIte]
    have := allN_spec eqS (l.toNat - 1) (by omega)
    refine rows5_congr fun i hi => ?_
    have e := Nat.eq_of_beq_eq_true (allN_spec this i hi)
    rw [e, Nat.add_eq, show 13 + (l.toNat - 1) = 12 + l.toNat by omega]
  · simp only [hp, ↓reduceIte]
    have := allN_spec eqSi ((-l).toNat - 1) (by omega)
    refine rows5_congr fun i hi => ?_
    have e := Nat.eq_of_beq_eq_true (allN_spec this i hi)
    rw [Nat.add_eq, show 17 + ((-l).toNat - 1) = 16 + (-l).toNat by omega] at e
    rw [e, Nat.add_eq, show 30 + ((-l).toNat - 1) = 29 + (-l).toNat by omega]

theorem word_R {w : List Int} {o : Nat} (hpl : plettersOK 17 w = true)
    (h : chainOK HNI.OP HNI.L HNI.R ltR 90 w o = true) :
    mword SA SIA w = rows5 (sr (o + w.length - 1)) := by
  refine chain5K_eq ok (fun l hl => ?_) h
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hpl
  exact mletter_R (hpl l hl).1 (hpl l hl).2

@[expose] noncomputable def blkB (b : Nat) : Bool :=
  HNI.OP (b + 5) == 0 && HNI.L (b + 5) == b && HNI.R (b + 5) == b + 1 &&
  HNI.OP (b + 6) == 0 && HNI.L (b + 6) == b + 2 && HNI.R (b + 6) == b + 3 &&
  HNI.OP (b + 7) == 0 && HNI.L (b + 7) == b && HNI.R (b + 7) == b + 4 &&
  HNI.OP (b + 8) == 0 && HNI.L (b + 8) == b + 7 && HNI.R (b + 8) == b + 2

theorem isId {k : Nat} (h : allN 133 (fun i => Nat.beq (sr k i) (idRow5 i)) = true) :
    (rows5 (sr k) == idM 133) = true :=
  eqId5_sound fun i hi => Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem blk {cs : Array (Array (Array Nat))} {M : Array (Array Nat)} {r e b : Nat}
    (hb : b + 9 ≤ 90) (he : e < 90)
    (hc : cs = #[rows5 (sr b), rows5 (sr (b + 1)), rows5 (sr (b + 2)), rows5 (sr (b + 3))])
    (hw : M = rows5 (sr e)) (hs : blkB b = true)
    (hsub : allN 133 (fun i => Nat.beq (sr (b + 4) i) (subRow5 (sr e) i)) = true)
    (hid1 : allN 133 (fun i => Nat.beq (sr (b + 5) i) (idRow5 i)) = true)
    (hid2 : allN 133 (fun i => Nat.beq (sr (b + 6) i) (idRow5 i)) = true)
    (hdg : allN 133 (fun i => Nat.beq (sr (b + 8) i) (diagRow5 r i)) = true) :
    rankCertOK (subId M) cs r = true := by
  subst hc
  simp only [blkB, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, b1⟩, b2⟩, b3⟩, c1⟩, c2⟩, c3⟩, d1⟩, d2⟩, d3⟩ := hs
  have e0 : (#[rows5 (sr b), rows5 (sr (b + 1)), rows5 (sr (b + 2)), rows5 (sr (b + 3))] :
      Array (Array (Array Nat)))[0]! = rows5 (sr b) := rfl
  have e1 : (#[rows5 (sr b), rows5 (sr (b + 1)), rows5 (sr (b + 2)), rows5 (sr (b + 3))] :
      Array (Array (Array Nat)))[1]! = rows5 (sr (b + 1)) := rfl
  have e2 : (#[rows5 (sr b), rows5 (sr (b + 1)), rows5 (sr (b + 2)), rows5 (sr (b + 3))] :
      Array (Array (Array Nat)))[2]! = rows5 (sr (b + 2)) := rfl
  have e3 : (#[rows5 (sr b), rows5 (sr (b + 1)), rows5 (sr (b + 2)), rows5 (sr (b + 3))] :
      Array (Array (Array Nat)))[3]! = rows5 (sr (b + 3)) := rfl
  have hsb : subId (rows5 (sr e)) = rows5 (sr (b + 4)) :=
    subId5_sound (canon e he) fun i hi => Nat.eq_of_beq_eq_true (allN_spec hsub i hi)
  unfold rankCertOK
  rw [e0, e1, e2, e3, hw, hsb, mul_eq (by omega) (by omega) (by omega) a1 a2 a3,
    mul_eq (by omega) (by omega) (by omega) b1 b2 b3,
    mul_eq (by omega) (by omega) (by omega) c1 c2 c3,
    mul_eq (by omega) (by omega) (by omega) d1 d2 d3,
    diag5_sound fun i hi => Nat.eq_of_beq_eq_true (allN_spec hdg i hi), isId hid1, isId hid2]
  simp

theorem ch1 : chainOK HNI.OP HNI.L HNI.R ltR 90 InvData.t2Word 34 = true := by quickRfl
theorem ch2 : chainOK HNI.OP HNI.L HNI.R ltR 90 InvData.t4Word 52 = true := by quickRfl

theorem bs1 : blkB 63 = true := by quickRfl
theorem bs2 : blkB 72 = true := by quickRfl
theorem bs3 : blkB 81 = true := by quickRfl

theorem pl1 : plettersOK 17 InvData.t2Word = true := by decide
theorem pl2 : plettersOK 17 InvData.t4Word = true := by decide

theorem pay (R : Nat → Nat) {s : String} {cs : List Char} (hs : s = String.ofList cs)
    (h : pay5K R cs = true) : rowsOf 5 133 s = rows5 R := by
  rw [hs]
  exact pay5_sound h

theorem cert1 : invRankRows[0]! =
    #[rows5 (sr 63), rows5 (sr (63 + 1)), rows5 (sr (63 + 2)), rows5 (sr (63 + 3))] := by
  have e : invRankRows[0]! = #[rowsOf 5 133 RankData.rankT2P, rowsOf 5 133 RankData.rankT2Pi,
      rowsOf 5 133 RankData.rankT2Q, rowsOf 5 133 RankData.rankT2Qi] := rfl
  rw [e, pay _ HNI1P.eq p1P, pay _ HNI1Pi.eq p1Pi, pay _ HNI1Q.eq p1Q, pay _ HNI1Qi.eq p1Qi]

theorem cert2 : invRankRows[1]! =
    #[rows5 (sr 72), rows5 (sr (72 + 1)), rows5 (sr (72 + 2)), rows5 (sr (72 + 3))] := by
  have e : invRankRows[1]! = #[rowsOf 5 133 RankData.rankT4P, rowsOf 5 133 RankData.rankT4Pi,
      rowsOf 5 133 RankData.rankT4Q, rowsOf 5 133 RankData.rankT4Qi] := rfl
  rw [e, pay _ HNI2P.eq p2P, pay _ HNI2Pi.eq p2Pi, pay _ HNI2Q.eq p2Q, pay _ HNI2Qi.eq p2Qi]

theorem cert3 : invRankRows[2]! =
    #[rows5 (sr 81), rows5 (sr (81 + 1)), rows5 (sr (81 + 2)), rows5 (sr (81 + 3))] := by
  have e : invRankRows[2]! = #[rowsOf 5 133 RankData.rankT6P, rowsOf 5 133 RankData.rankT6Pi,
      rowsOf 5 133 RankData.rankT6Q, rowsOf 5 133 RankData.rankT6Qi] := rfl
  rw [e, pay _ HNI3P.eq p3P, pay _ HNI3Pi.eq p3Pi, pay _ HNI3Q.eq p3Q, pay _ HNI3Qi.eq p3Qi]

theorem len1 : 34 + InvData.t2Word.length - 1 = 51 := by decide
theorem len2 : 52 + InvData.t4Word.length - 1 = 61 := by decide

theorem a_eq : rowsA = rows5 (sr 62) := by
  rw [rowsA_eq]
  exact rows5_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec eqA i hi)).symm

theorem facts2090 : invRankChecks rowsA rowsB invRankRows = true := by
  have hw1 := word_R pl1 ch1
  rw [len1] at hw1
  have hw2 := word_R pl2 ch2
  rw [len2] at hw2
  unfold invRankChecks invRankChecksH
  rw [strong_eq]
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨rfl, pl1⟩, pl2⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [cert1]
    exact blk (by omega) (by omega) rfl hw1 bs1 sub1 idP1 idQ1 dg1
  · rw [cert2]
    exact blk (by omega) (by omega) rfl hw2 bs2 sub2 idP2 idQ2 dg2
  · rw [cert3]
    exact blk (by omega) (by omega) rfl a_eq bs3 sub3 idP3 idQ3 dg3

end CertificateChecks.KernelSpor.HN2090

end
