module

public import Certificates.Kernel.J2Cover.M22S
public import Certificates.Kernel.J2Cover.M22Fold
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Models CFSG.KC.J2Cover
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.Monster.B.Co2 (allLt_iff)

theorem cntR_congr {p q : Nat → Bool} : ∀ n, (∀ i < n, p i = q i) → cntR p n = cntR q n
  | 0, _ => rfl
  | n + 1, h => by
    change Nat.add (cntR p n) (Bool.rec 0 1 (p n)) = Nat.add (cntR q n) (Bool.rec 0 1 (q n))
    rw [cntR_congr n fun i hi => h i (by omega), h n (by omega)]

@[expose] noncomputable def fixP (X : Nat) : Nat := cntR (fun i => pg 9 (mask 9) X i == i) 315

theorem fixCount_unpack (X : Nat) : fixCountArr (unpack 315 9 X) = fixP X := by
  unfold fixCountArr fixP
  rw [countFold_eq]
  refine cntR_congr 315 fun i hi => ?_
  rw [getElem!_unpack hi]

@[expose] noncomputable def fIV (a : Nat) : Bool :=
  bIf(Nat.beq a 0, true, bIf(Nat.beq (mtK a a) 0,
    bAnd(bIf(Nat.beq (conjOf a).1 4,
        bAnd(Nat.beq (fixP (ELT a)) 11, bIf((fRK a).testBit a, false, true)),
        bAnd(Nat.beq (conjOf a).1 2, bAnd(Nat.beq (fixP (ELT a)) 15, (fRK a).testBit a))),
      Nat.beq (pcomp 315 9 (mask 9) (wordP (conjOf a).2) (ELT a))
        (pcomp 315 9 (mask 9) (ELT (conjOf a).1) (wordP (conjOf a).2))), true))

#lc_blocks IVB fIV 128 8

theorem iv_facts (a : Nat) (ha : a < 128) (h0 : a ≠ 0) (hm : mtK a a = 0) :
    (((conjOf a).1 = 4 ∧ fixP (ELT a) = 11 ∧ (fRK a).testBit a = false) ∨
      ((conjOf a).1 = 2 ∧ fixP (ELT a) = 15 ∧ (fRK a).testBit a = true)) ∧
    pcomp 315 9 (mask 9) (wordP (conjOf a).2) (ELT a) =
      pcomp 315 9 (mask 9) (ELT (conjOf a).1) (wordP (conjOf a).2) := by
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) IVB.all a ha
  unfold fIV at h
  have e0 : Nat.beq (mtK a a) 0 = true := by
    rw [hm]
    rfl
  rw [beq_false h0, e0] at h
  dsimp only at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨?_, Nat.eq_of_beq_eq_true h2⟩
  cases hc : Nat.beq (conjOf a).1 4
  · rw [hc] at h1
    dsimp only at h1
    obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
    exact Or.inr ⟨Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, h5⟩
  · rw [hc] at h1
    dsimp only at h1
    obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h1
    refine Or.inl ⟨Nat.eq_of_beq_eq_true hc, Nat.eq_of_beq_eq_true h4, ?_⟩
    cases ht : (fRK a).testBit a
    · rfl
    · rw [ht] at h5
      exact absurd h5 (by decide)

theorem invC : involCheck = true := by
  have q1 : (fixCountArr eltArrs[4]! == 11) = true := by
    rw [eltArrs_eq 4 (by norm_num), fixCount_unpack]
    quickRfl
  have q2 : (fixCountArr eltArrs[2]! == 15) = true := by
    rw [eltArrs_eq 2 (by norm_num), fixCount_unpack]
    quickRfl
  unfold involCheck
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨q1, q2⟩, allLt_iff.2 fun a ha => ?_⟩
  dsimp only
  by_cases h0 : a = 0
  · subst h0
    rfl
  by_cases hm : mtK a a = 0
  · obtain ⟨hc, he⟩ := iv_facts a ha h0 hm
    have hfr : fRows[a]! = fRK a := congrFun fR_eq a
    rw [mt_pt, hm]
    generalize conjOf a = cw at hc he ⊢
    obtain ⟨t, w⟩ := cw
    dsimp only at hc he ⊢
    have ht : t < 128 := by
      rcases hc with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    unfold bitAt
    rw [eltArrs_eq a ha, eltArrs_eq t ht, wordArr_eq, fixCount_unpack, hfr,
      compA_unpackN (wordP_canon w) (eltT_canon a ha), compA_unpackN (eltT_canon t ht) (wordP_canon w),
      eqA_unpackN (canon_pcN (wordP_canon w) (eltT_canon a ha))
        (canon_pcN (eltT_canon t ht) (wordP_canon w)), he, Nat.beq_refl]
    rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3]
  · have hm' : ((mulTab[a]!)[a]! != 0) = true := by
      rw [mt_pt]
      simpa using hm
    rw [Bool.or_eq_true, Bool.or_eq_true]
    exact Or.inl (Or.inr hm')

theorem cBB : CnN 315 9 BB := by quickRfl

theorem sigmaT_eq : sigmaT = unpack 4725 13 SGP := natsOf_bind NSG.eq (by quickRfl) (by quickRfl)

theorem kO5 : allN 128 (fun a => bAnd(Nat.blt (betaIdx a) 128,
    Nat.beq (pcomp 315 9 (mask 9) BB (pcomp 315 9 (mask 9) (ELT a) BB)) (ELT (betaIdx a)))) = true := by
  quickRfl

@[expose] noncomputable def fOR (i : Nat) : Bool :=
  strictB (pg 13 (mask 13) SGP i) fun s => strictB (pg 13 (mask 13) ACP i) fun c =>
    bAnd(Nat.blt s 4725, bAnd(Nat.blt c 128,
      Nat.beq (pcomp 315 9 (mask 9) BB (pcomp 315 9 (mask 9) (RPT i) BB))
        (pcomp 315 9 (mask 9) (ELT c) (RPT s))))

#lc_blocks ORB fOR 4725 64

theorem kO7 : allN 4725 (fun i => i == 0 || i == 17 || i == 20 || iK i 1 != i || iK i 2 != i ||
    iK i 3 != i) = true := by quickRfl

theorem kO8 : allN 3 (fun r => allN 128 fun k =>
    !(Nat.beq BB (pcomp 315 9 (mask 9) (ELT k) (RPT (nth 0 [0, 17, 20] r))))) = true := by quickRfl

theorem outC : outerCheck = true := by
  have p1 : isInvA 315 outerU outerU = true := by
    rw [hOUM]
    exact (invEqK_sound (n := 315) (w := 9) (p := OU) (r := OU) (by quickRfl)).2
  have p2 : isInvA 315 (letterArr 1) bInvArr = true := by
    have e : letterArr 1 = unpack 315 9 (PA.S 1) := letter_eq 1
    unfold bInvArr
    rw [e, (invEqK_sound (allN_spec perm 1 (by omega))).1]
    exact (invEqK_sound (allN_spec perm 1 (by omega))).2
  have p3 : eqA 315 (compA 315 bArr (compA 315 (letterArr 0) bArr)) repArrs[14]! = true := by
    rw [bArr_eq, letter_eq, repArrs_eq 14 (by norm_num), compA_unpackN (letP_canon 0) cBB,
      compA_unpackN cBB (canon_pcN (letP_canon 0) cBB),
      eqA_unpackN (canon_pcN cBB (canon_pcN (letP_canon 0) cBB)) (repT_canon 14 (by norm_num))]
    quickRfl
  have p4 : eqA 315 (compA 315 bArr (compA 315 (letterArr 1) bArr)) repArrs[5]! = true := by
    rw [bArr_eq, letter_eq, repArrs_eq 5 (by norm_num), compA_unpackN (letP_canon 1) cBB,
      compA_unpackN cBB (canon_pcN (letP_canon 1) cBB),
      eqA_unpackN (canon_pcN cBB (canon_pcN (letP_canon 1) cBB)) (repT_canon 5 (by norm_num))]
    quickRfl
  have p5 : allLt 128 (fun a => decide (betaIdx a < 128) &&
      eqA 315 (compA 315 bArr (compA 315 eltArrs[a]! bArr)) eltArrs[betaIdx a]!) = true := by
    refine allLt_iff.2 fun a ha => ?_
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kO5 a ha)
    have hb : betaIdx a < 128 := Nat.le_of_ble_eq_true h1
    rw [bArr_eq, eltArrs_eq a ha, eltArrs_eq _ hb, compA_unpackN (eltT_canon a ha) cBB,
      compA_unpackN cBB (canon_pcN (eltT_canon a ha) cBB),
      eqA_unpackN (canon_pcN cBB (canon_pcN (eltT_canon a ha) cBB)) (eltT_canon _ hb), h2]
    simp [hb]
  have p6 : allLt 4725 (fun i => decide (sigmaT[i]! < 4725) && decide (aCoefT[i]! < 128) &&
      eqA 315 (compA 315 bArr (compA 315 repArrs[i]! bArr))
        (compA 315 eltArrs[aCoefT[i]!]! repArrs[sigmaT[i]!]!)) = true := by
    refine allLt_iff.2 fun i hi => ?_
    have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) ORB.all i hi
    unfold fOR at h
    rw [strictB_eq', strictB_eq'] at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
    have hs : pg 13 (mask 13) SGP i < 4725 := Nat.le_of_ble_eq_true h1
    have hc : pg 13 (mask 13) ACP i < 128 := Nat.le_of_ble_eq_true h2
    rw [sigmaT_eq, aCoefT_eq, getElem!_unpack hi, getElem!_unpack hi, bArr_eq, repArrs_eq i hi,
      eltArrs_eq _ hc, repArrs_eq _ hs, compA_unpackN (repT_canon i hi) cBB,
      compA_unpackN cBB (canon_pcN (repT_canon i hi) cBB),
      compA_unpackN (eltT_canon _ hc) (repT_canon _ hs),
      eqA_unpackN (canon_pcN cBB (canon_pcN (repT_canon i hi) cBB))
        (canon_pcN (eltT_canon _ hc) (repT_canon _ hs)), h3]
    simp [hs, hc]
  have p7 : allLt 4725 (fun i => i == 0 || i == 17 || i == 20 || iTab i 1 != i || iTab i 2 != i ||
      iTab i 3 != i) = true := by
    rw [iT_eq, allLt_eq_allN]
    exact kO7
  have p8 : [0, 17, 20].all (fun i => allLt 128 fun k =>
      !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[i]!))) = true := by
    have one : ∀ r < 3, allLt 128 (fun k =>
        !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[nth 0 [0, 17, 20] r]!))) = true := by
      intro r hr
      have hi : nth 0 [0, 17, 20] r < 4725 := by
        interval_cases r <;> decide
      refine allLt_iff.2 fun k hk => ?_
      rw [bArr_eq, eltArrs_eq k hk, repArrs_eq _ hi, compA_unpackN (eltT_canon k hk) (repT_canon _ hi),
        eqA_unpackN cBB (canon_pcN (eltT_canon k hk) (repT_canon _ hi))]
      exact allN_spec (allN_spec kO8 r hr) k hk
    have e : [0, 17, 20].all (fun i => allLt 128 fun k =>
        !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[i]!))) =
        (allLt 128 (fun k => !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[nth 0 [0, 17, 20] 0]!))) &&
        (allLt 128 (fun k => !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[nth 0 [0, 17, 20] 1]!))) &&
        (allLt 128 (fun k => !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[nth 0 [0, 17, 20] 2]!))) &&
          true))) := rfl
    rw [e, one 0 (by omega), one 1 (by omega), one 2 (by omega)]
    rfl
  unfold outerCheck
  rw [p1, p2, p3, p4, p5, p6, p7, p8]
  rfl

end CertificateChecks.KernelJ2Cover

end
