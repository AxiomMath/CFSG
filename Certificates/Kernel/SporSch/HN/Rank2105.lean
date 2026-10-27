module

public import Certificates.Kernel.SporSch.HN.Rank2105K
public import Certificates.Kernel.SporSch.HN.Strong
public import CFSG.Certificates.Kernel.SporSch.HNF5RankKronSound
public import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNRank

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNSchreier CFSG.ONSchreier.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HNStrong

theorem ok (k : Nat) (hk : k < 132) : KrOK HNR.MT HNR.OP HNR.L HNR.R k := by
  rcases (by omega : k < 35 ∨ (35 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 61) ∨ (61 ≤ k ∧ k < 70) ∨
      (70 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 114) ∨
      114 ≤ k) with h | h | h | h | h | h | h | h | h
  · exact krOK_of_blk blk0 (by omega) (by omega)
  · exact krOK_of_blk blk1 (by omega) (by omega)
  · exact krOK_of_blk blk2 (by omega) (by omega)
  · exact krOK_of_blk blk3 (by omega) (by omega)
  · exact krOK_of_blk blk4 (by omega) (by omega)
  · exact krOK_of_blk blk5 (by omega) (by omega)
  · exact krOK_of_blk blk6 (by omega) (by omega)
  · exact krOK_of_blk blk7 (by omega) (by omega)
  · exact krOK_of_blk blk8 (by omega) (by omega)

theorem canon (k : Nat) (hk : k < 132) : Canon5 (sr k) := (ok k hk).1

theorem mul_eq {K l r : Nat} (hl1 : l < 132) (hr1 : r < 132) (hK : K < 132) (ho : HNR.OP K = 0)
    (hl : HNR.L K = l) (hr : HNR.R K = r) :
    mulM 5 133 (rows5 (sr l)) (rows5 (sr r)) = rows5 (sr K) :=
  krOK_mul (ok K hK) (canon l hl1) (canon r hr1) ho hl hr

@[expose] def ltR (l : Int) : Nat := if 0 < l then l.toNat - 1 else 16 + (-l).toNat

theorem mletter_R {l : Int} (h0 : l ≠ 0) (h17 : l.natAbs ≤ 17) :
    mletter SA SIA l = rows5 (sr (ltR l)) := by
  rw [mletter_eq h0 h17, letK, ltR]
  by_cases hp : 0 < l
  · rw [if_pos hp, if_pos hp]
    have := allN_spec eqS (l.toNat - 1) (by omega)
    refine rows5_congr fun i hi => ?_
    have e := Nat.eq_of_beq_eq_true (allN_spec this i hi)
    rw [e, Nat.add_eq, show 13 + (l.toNat - 1) = 12 + l.toNat by omega]
  · rw [if_neg hp, if_neg hp]
    have := allN_spec eqSi ((-l).toNat - 1) (by omega)
    refine rows5_congr fun i hi => ?_
    have e := Nat.eq_of_beq_eq_true (allN_spec this i hi)
    rw [Nat.add_eq, show 17 + ((-l).toNat - 1) = 16 + (-l).toNat by omega] at e
    rw [e, Nat.add_eq, show 30 + ((-l).toNat - 1) = 29 + (-l).toNat by omega]

theorem word_R {w : List Int} {o : Nat} (hpl : plettersOK 17 w = true)
    (h : chainOK HNR.OP HNR.L HNR.R ltR 132 w o = true) :
    mword SA SIA w = rows5 (sr (o + w.length - 1)) := by
  refine chain5K_eq ok (fun l hl => ?_) h
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hpl
  exact mletter_R (hpl l hl).1 (hpl l hl).2

@[expose] noncomputable def blkB (b : Nat) : Bool :=
  HNR.OP (b + 5) == 0 && HNR.L (b + 5) == b && HNR.R (b + 5) == b + 1 &&
  HNR.OP (b + 6) == 0 && HNR.L (b + 6) == b + 2 && HNR.R (b + 6) == b + 3 &&
  HNR.OP (b + 7) == 0 && HNR.L (b + 7) == b && HNR.R (b + 7) == b + 4 &&
  HNR.OP (b + 8) == 0 && HNR.L (b + 8) == b + 7 && HNR.R (b + 8) == b + 2

theorem isId {k : Nat} (h : allN 133 (fun i => Nat.beq (sr k i) (idRow5 i)) = true) :
    (rows5 (sr k) == idM 133) = true :=
  eqId5_sound fun i hi => Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem blk {cs : Array (Array (Array Nat))} {w : List Int} {r e b : Nat} (hb : b + 9 ≤ 132)
    (he : e < 132)
    (hc : cs = #[rows5 (sr b), rows5 (sr (b + 1)), rows5 (sr (b + 2)), rows5 (sr (b + 3))])
    (hw : mword SA SIA w = rows5 (sr e)) (hpl : plettersOK 17 w = true)
    (hs : blkB b = true)
    (hsub : allN 133 (fun i => Nat.beq (sr (b + 4) i) (subRow5 (sr e) i)) = true)
    (hid1 : allN 133 (fun i => Nat.beq (sr (b + 5) i) (idRow5 i)) = true)
    (hid2 : allN 133 (fun i => Nat.beq (sr (b + 6) i) (idRow5 i)) = true)
    (hdg : allN 133 (fun i => Nat.beq (sr (b + 8) i) (diagRow5 r i)) = true) :
    (cs.size == 4 && plettersOK 17 w && mulM 5 133 cs[0]! cs[1]! == idM 133 &&
      mulM 5 133 cs[2]! cs[3]! == idM 133 &&
      mulM 5 133 (mulM 5 133 cs[0]! (subId (mword SA SIA w))) cs[2]! == diagR r) = true := by
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
  rw [e0, e1, e2, e3, hw, hsb, mul_eq (by omega) (by omega) (by omega) a1 a2 a3,
    mul_eq (by omega) (by omega) (by omega) b1 b2 b3,
    mul_eq (by omega) (by omega) (by omega) c1 c2 c3,
    mul_eq (by omega) (by omega) (by omega) d1 d2 d3,
    diag5_sound fun i hi => Nat.eq_of_beq_eq_true (allN_spec hdg i hi), isId hid1, isId hid2, hpl]
  simp

theorem ch1 : chainOK HNR.OP HNR.L HNR.R ltR 132 FAData.sWords[0]! 34 = true := by quickRfl
theorem ch2 : chainOK HNR.OP HNR.L HNR.R ltR 132 FAData.sWords[1]! 44 = true := by quickRfl
theorem ch3 : chainOK HNR.OP HNR.L HNR.R ltR 132 FAData.sWords[2]! 61 = true := by quickRfl
theorem ch4 : chainOK HNR.OP HNR.L HNR.R ltR 132 FAData.sWords[3]! 78 = true := by quickRfl

theorem bs1 : blkB 96 = true := by quickRfl
theorem bs2 : blkB 105 = true := by quickRfl
theorem bs3 : blkB 114 = true := by quickRfl
theorem bs4 : blkB 123 = true := by quickRfl

theorem pl1 : plettersOK 17 FAData.sWords[0]! = true := by decide
theorem pl2 : plettersOK 17 FAData.sWords[1]! = true := by decide
theorem pl3 : plettersOK 17 FAData.sWords[2]! = true := by decide
theorem pl4 : plettersOK 17 FAData.sWords[3]! = true := by decide

theorem pay (R : Nat → Nat) {s : String} {cs : List Char} (hs : s = String.ofList cs)
    (h : pay5K R cs = true) : rowsOf 5 133 s = rows5 R := by
  rw [hs]
  exact pay5_sound h

theorem cert1 : rankCertRows[0]! =
    #[rows5 (sr 96), rows5 (sr (96 + 1)), rows5 (sr (96 + 2)), rows5 (sr (96 + 3))] := by
  have e : rankCertRows[0]! = #[rowsOf 5 133 RankData.rank1P, rowsOf 5 133 RankData.rank1Pi,
      rowsOf 5 133 RankData.rank1Q, rowsOf 5 133 RankData.rank1Qi] := rfl
  rw [e, pay _ HNR1P.eq p1P, pay _ HNR1Pi.eq p1Pi, pay _ HNR1Q.eq p1Q, pay _ HNR1Qi.eq p1Qi]

theorem cert2 : rankCertRows[1]! =
    #[rows5 (sr 105), rows5 (sr (105 + 1)), rows5 (sr (105 + 2)), rows5 (sr (105 + 3))] := by
  have e : rankCertRows[1]! = #[rowsOf 5 133 RankData.rank2P, rowsOf 5 133 RankData.rank2Pi,
      rowsOf 5 133 RankData.rank2Q, rowsOf 5 133 RankData.rank2Qi] := rfl
  rw [e, pay _ HNR2P.eq p2P, pay _ HNR2Pi.eq p2Pi, pay _ HNR2Q.eq p2Q, pay _ HNR2Qi.eq p2Qi]

theorem cert3 : rankCertRows[2]! =
    #[rows5 (sr 114), rows5 (sr (114 + 1)), rows5 (sr (114 + 2)), rows5 (sr (114 + 3))] := by
  have e : rankCertRows[2]! = #[rowsOf 5 133 RankData.rank3P, rowsOf 5 133 RankData.rank3Pi,
      rowsOf 5 133 RankData.rank3Q, rowsOf 5 133 RankData.rank3Qi] := rfl
  rw [e, pay _ HNR3P.eq p3P, pay _ HNR3Pi.eq p3Pi, pay _ HNR3Q.eq p3Q, pay _ HNR3Qi.eq p3Qi]

theorem cert4 : rankCertRows[3]! =
    #[rows5 (sr 123), rows5 (sr (123 + 1)), rows5 (sr (123 + 2)), rows5 (sr (123 + 3))] := by
  have e : rankCertRows[3]! = #[rowsOf 5 133 RankData.rank4P, rowsOf 5 133 RankData.rank4Pi,
      rowsOf 5 133 RankData.rank4Q, rowsOf 5 133 RankData.rank4Qi] := rfl
  rw [e, pay _ HNR4P.eq p4P, pay _ HNR4Pi.eq p4Pi, pay _ HNR4Q.eq p4Q, pay _ HNR4Qi.eq p4Qi]

theorem len1 : 34 + FAData.sWords[0]!.length - 1 = 43 := by decide
theorem len2 : 44 + FAData.sWords[1]!.length - 1 = 60 := by decide
theorem len3 : 61 + FAData.sWords[2]!.length - 1 = 77 := by decide
theorem len4 : 78 + FAData.sWords[3]!.length - 1 = 95 := by decide

theorem facts : rankChecks rowsA rowsB rankCertRows = true := by
  have hb : ∀ k < 4, (rankCertRows[k]!.size == 4 && plettersOK 17 FAData.sWords[k]! &&
      mulM 5 133 (rankCertRows[k]!)[0]! (rankCertRows[k]!)[1]! == idM 133 &&
      mulM 5 133 (rankCertRows[k]!)[2]! (rankCertRows[k]!)[3]! == idM 133 &&
      mulM 5 133 (mulM 5 133 (rankCertRows[k]!)[0]! (subId (mword SA SIA FAData.sWords[k]!)))
        (rankCertRows[k]!)[2]! == diagR rankList[k]!) = true := by
    intro k hk
    interval_cases k
    · have hw := word_R pl1 ch1
      rw [len1] at hw
      exact blk (r := 84) (by omega) (by omega) cert1 hw pl1 bs1 sub1 idP1 idQ1 dg1
    · have hw := word_R pl2 ch2
      rw [len2] at hw
      exact blk (r := 84) (by omega) (by omega) cert2 hw pl2 bs2 sub2 idP2 idQ2 dg2
    · have hw := word_R pl3 ch3
      rw [len3] at hw
      exact blk (r := 90) (by omega) (by omega) cert3 hw pl3 bs3 sub3 idP3 idQ3 dg3
    · have hw := word_R pl4 ch4
      rw [len4] at hw
      exact blk (r := 84) (by omega) (by omega) cert4 hw pl4 bs4 sub4 idP4 idQ4 dg4
  unfold rankChecks
  dsimp only
  rw [strong_eq, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨rfl, rfl⟩, CFSG.ONSchreier.allBelowN_iff.2 hb⟩

end CertificateChecks.KernelSporSch.HNRank

end
