
module

public import Certificates.Kernel.Sporadic.L2.G6

public section

namespace CertificateChecks.KernelSpor.L2G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ElimCert CFSG.Sporadic.SuzRecog
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)
open CFSG.ComponentClassification.AS81.SuzB0

local notation "pgk" => pg 11 (mask 11)
local notation "pc" => pcomp 1782 11 (mask 11)

theorem qE_get {j x : Nat} (hj : j < 128) (hx : x < 1782) : (qElts[j]!)[x]! = qEK j x := by
  unfold qElts
  rw [getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj), Array.getElem_ofFn]
  simp only
  rw [CFSG.Monster.B.Co2.compA_get hx]
  have hq : qProds[j / 2]! = qProd (j / 2) := by
    unfold qProds
    rw [getElem!_pos _ (j / 2) (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  rw [hq]
  unfold qEK tPow
  rw [show Nat.div j 2 = j / 2 from rfl, show Nat.mod j 2 = j % 2 from rfl]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, Q3AG.nIf_eq]
    simp only [show ((0 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false,
      show Nat.beq 0 1 = false from rfl]
    rw [CFSG.PSL3Four.Native.idTab, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
    exact SuzWF.qProd_get hx
  · rw [h, Q3AG.nIf_eq]
    simp only [show ((1 : Nat) == 1) = true from rfl, if_true,
      show Nat.beq 1 1 = true from rfl]
    have ht : tTab[x]! = pgk T1 x := by
      change t1Arr[x]! = _
      rw [pT1.1, CFSG.KC.HeFixK.unpack_getElem! hx]
    rw [ht]
    exact SuzWF.qProd_get (CFSG.KC.HeFixK.pg_lt_of_canonK pT1.2 hx)

theorem fp_qE {j : Nat} (hj : j < 128) : fp qElts[j]! = fQ j := by
  unfold fp fQ
  rw [qE_get hj (by norm_num), qE_get hj (by norm_num), qE_get hj (by norm_num),
    qE_get hj (by norm_num), qE_get hj (by norm_num), qE_get hj (by norm_num)]
  rfl

theorem allLt_eq {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) : allLt n f = allN n g := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro h1
    exact CFSG.KS.Raw.allN_of_forall fun i hi => (h i hi) ▸ allLt_spec h1 hi
  · intro h2
    exact allLt_iff.2 fun i hi => (h i hi).symm ▸ allN_get h2 hi

theorem eqA_qE {y j : Nat} (hy : y < 2835) (hj : j < 128) : eqA 1782 aPts[y]! qElts[j]! = eqQ y j := by
  unfold eqA eqQ
  refine allLt_eq fun x hx => ?_
  rw [(pA (hvA vtxOK) hy).1, CFSG.KC.HeFixK.unpack_getElem! hx, qE_get hj hx, Q3AG.beqN]

theorem getD_absent (L : List (Nat × Nat)) (m : Std.HashMap Nat Nat) {k d : Nat}
    (h : ∀ p ∈ L, p.1 ≠ k) : (L.foldl (fun m p => m.insert p.1 p.2) m).getD k d = m.getD k d := by
  induction L generalizing m with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldl_cons, ih _ fun p hp => h p (List.mem_cons_of_mem _ hp), Std.HashMap.getD_insert,
      if_neg (by simpa using h a (List.mem_cons_self))]

theorem aIdx_absent {f : Nat} (h : ∀ i < 2835, fA i ≠ f) : aIdx.getD f 2835 = 2835 := by
  unfold aIdx
  rw [fpTable_eq, aPts_size, getD_absent, Std.HashMap.getD_empty]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  have hi' := List.mem_range.1 hi
  rw [fp_A (hvA vtxOK) hi']
  exact h i hi'

theorem sort_parts : (∀ a b, a < b → b < 2835 → fA (ordA a) < fA (ordA b)) ∧
    ∀ i < 2835, posA i < 2835 ∧ ordA (posA i) = i := by
  have h := kSortA
  unfold sortK at h
  rw [band] at h
  refine ⟨sort_mono h.1, fun i hi => ?_⟩
  have := allN_get h.2 hi
  rw [sB, band, nblt, nbeq] at this
  exact this

theorem absent_of_gap {f m : Nat} (hm : m ≤ 2835) (h1 : m = 0 ∨ fA (ordA (m - 1)) < f)
    (h2 : m = 2835 ∨ f < fA (ordA m)) : ∀ i < 2835, fA i ≠ f := by
  obtain ⟨hmono, hpos⟩ := sort_parts
  intro i hi he
  obtain ⟨hp, hpi⟩ := hpos i hi
  rw [← hpi] at he
  by_cases hlt : posA i < m
  · rcases h1 with h0 | h1
    · omega
    · rcases Nat.lt_or_ge (posA i) (m - 1) with h3 | h3
      · have := hmono _ _ h3 (by omega)
        omega
      · have e : posA i = m - 1 := by omega
        rw [e] at he
        omega
  · rcases h2 with h0 | h2
    · omega
    · rcases Nat.lt_or_ge m (posA i) with h3 | h3
      · have := hmono _ _ h3 hp
        omega
      · have e : posA i = m := by omega
        rw [e] at he
        omega

theorem ex_of_occK {y : Nat} (h : occK 0 y = true) : ∃ k < 36, nbK 0 k = y := by
  unfold occK at h
  rw [show Nat.blt 0 2835 = true from rfl] at h
  change (Bool.not (allN 36 fun k => Bool.not (Nat.beq (nbK 0 k) y))) = true at h
  by_contra hno
  rw [Bool.not_eq_true', Bool.eq_false_iff] at h
  apply h
  refine CFSG.KS.Raw.allN_of_forall fun k hk => ?_
  rw [Q3AG.nbeq_false (fun e => hno ⟨k, hk, e⟩)]
  rfl

theorem n0_of_adj {y : Nat} (h : adjK 0 y = true) : ∃ k < 36, nbK 0 k = y := by
  have k0 := kNbP
  unfold nbPK at k0
  rw [band, band, band] at k0
  by_cases hy : y < 2997
  · have h1 := not_or_of (allN_get k0.2.2.2 hy)
    rw [h] at h1
    exact ex_of_occK h1
  · unfold adjK at h
    rw [band, bif_true] at h
    apply ex_of_occK
    cases ho : occK 0 y
    · have := h.2.2 ho
      unfold occK at this
      rw [nblt_f (show ¬ y < 2835 by omega)] at this
      exact absurd this Bool.false_ne_true
    · rfl

theorem groupK_parts : pc (TK 0 0) (TK 0 1) = TK 0 2 ∧ commK2 (L2A 342) T1 = true ∧
    fA 680 = fpK 11 (mask 11) (pc T1 (L2A 342)) ∧ L2A 680 = pc T1 (L2A 342) ∧
    adjK 680 2852 = true := by
  have h := kGroup
  unfold groupK at h
  rw [band, band, sB, band, band, nbeq, nbeq, nbeq] at h
  exact h

theorem w0_eq : w0Arr = wPts[0]! := by
  rw [pW0.1, (pW (hvW vtxOK) (by norm_num)).1,
    (tVt_parts (hvW vtxOK 0 (by norm_num))).1 rfl]

theorem groupOK_true : groupOK = true := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := groupK_parts
  have hw := hvW vtxOK
  have hv := hvA vtxOK
  have T0 := pT hw (j := 0) (k := 0) (by norm_num) (by norm_num)
  have T1' := pT hw (j := 0) (k := 1) (by norm_num) (by norm_num)
  have T2' := pT hw (j := 0) (k := 2) (by norm_num) (by norm_num)
  have e1 : rhoConj w0Arr = (trip 0)[1]! := by rw [trip_eq (by norm_num), tripOf_get1, w0_eq]; rfl
  have e2 : rhoConj (rhoConj w0Arr) = (trip 0)[2]! := by
    rw [trip_eq (by norm_num), tripOf_get2, w0_eq]; rfl
  have e0 : w0Arr = (trip 0)[0]! := by rw [trip_eq (by norm_num), tripOf_get0, w0_eq]
  have N : (allLt 2997 fun y => !adjB nbr 0 y ||
      (if y < 2835 then y != 0 && (List.range 128).any fun j => eqA 1782 aPts[y]! qElts[j]!
       else commA t1Arr wPts[y - 2835]!)) = true := allLt_iff.2 fun y hy => by
    cases ha : adjB nbr 0 y
    · rfl
    obtain ⟨k, hk, hyk⟩ := n0_of_adj (by rw [← adjB_eq]; exact ha)
    have h := nb0All k hk
    unfold nb0Q at h
    rw [sB, hyk] at h
    simp only [Bool.not_true, Bool.false_or]
    by_cases hlt : y < 2835
    · rw [if_pos hlt]
      rw [show Nat.blt y 2835 = true from nblt.2 hlt, band] at h
      obtain ⟨h1, h2⟩ := h
      refine Bool.and_eq_true_iff.2 ⟨by rw [bne_eq]; exact h1, ?_⟩
      rw [List.any_eq_true]
      by_contra hno
      rw [Bool.not_eq_true', Bool.eq_false_iff] at h2
      apply h2
      refine CFSG.KS.Raw.allN_of_forall fun j hj => ?_
      cases hb : eqQ y j
      · rfl
      · exact absurd ⟨j, List.mem_range.2 hj, by rw [eqA_qE hlt hj]; exact hb⟩ hno
    · rw [if_neg hlt]
      rw [nblt_f hlt] at h
      have hj : y - 2835 < 162 := by omega
      rw [commA_P2 pT1 (pW hw hj)]
      exact h
  have Q : (allLt 128 fun j => let i := aIdx.getD (fp qElts[j]!) 2835
      !(decide (i < 2835) && i != 0 && eqA 1782 aPts[i]! qElts[j]!) || adjB nbr 0 i) = true :=
    allLt_iff.2 fun j hj => by
      have h := slices (len := 16) (k := 8) (by norm_num) (by norm_num) qAll j hj
      unfold qChk at h
      rw [sB, sB] at h
      simp only
      rw [fp_qE hj]
      generalize bsA (fQ j) 13 0 2835 = m at h
      rw [bif_true] at h
      by_cases hf : m < 2835 ∧ fA (ordA m) = fQ j
      · have h' := h.1 (by rw [band, nblt, nbeq]; exact hf)
        rw [sB, band, nblt] at h'
        obtain ⟨hi, hc⟩ := h'
        rw [← hf.2, aIdx_get hv kSortA hi]
        rw [bif_true] at hc
        cases hq : bAnd(Bool.not (Nat.beq (ordA m) 0), eqQ (ordA m) j)
        · by_cases h0 : ordA m = 0
          · simp [h0]
          · have : eqQ (ordA m) j = false := by
              rw [Bool.eq_false_iff]
              intro hne
              rw [Q3AG.nbeq_false h0, hne] at hq
              exact Bool.false_ne_true hq.symm
            rw [eqA_qE hi hj, this]
            simp
        · have := hc.1 hq
          rw [adjB_eq, this]
          simp
      · have h' := h.2 (by
          cases hb : bAnd(Nat.blt m 2835, Nat.beq (fA (ordA m)) (fQ j))
          · rfl
          · rw [band, nblt, nbeq] at hb
            exact absurd hb hf)
        rw [band, band, nble, bif_true, bif_true] at h'
        obtain ⟨hm, h1, h2⟩ := h'
        have g1' : m = 0 ∨ fA (ordA (m - 1)) < fQ j := by
          by_cases h0 : m = 0
          · exact Or.inl h0
          · have := h1.2 (Q3AG.nbeq_false h0)
            rw [nblt, Nat.pred_eq_sub_one] at this
            exact Or.inr this
        have g2' : m = 2835 ∨ fQ j < fA (ordA m) := by
          by_cases h0 : m = 2835
          · exact Or.inl h0
          · exact Or.inr (nblt.1 (h2.2 (Q3AG.nbeq_false h0)))
        have hab := absent_of_gap hm g1' g2'
        rw [aIdx_absent hab]
        simp
  have W : (allLt 162 fun j => !commA t1Arr wPts[j]! || adjB nbr 0 (2835 + j)) = true :=
    allLt_iff.2 fun j hj => by
      have h := slices (len := 16) (k := 11) (by norm_num) (by norm_num) wcAll j hj
      rw [show Nat.blt j 162 = true from nblt.2 hj] at h
      change bIf(commK2 T1 (TK j 0), adjK 0 (Nat.add 2835 j), true) = true at h
      rw [commA_P2 pT1 (pW hw hj), adjB_eq]
      exact not_or_of h
  have hp1 := p1_eq
  have hB : P bArr (pc T1 (L2A 342)) := by
    unfold bArr
    rw [hp1]
    exact p_comp pT1 (pA hv (by norm_num))
  have hbIdx : bIdx = 680 := by
    unfold bIdx
    rw [hB.1, fp_unpack, ← g3]
    exact aIdx_get hv kSortA (by norm_num)
  unfold groupOK
  simp only [Bool.and_eq_true, N, Q, W, true_and, and_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [e2, e1, e0, eqA_P (p_comp T0 T1') T2', g1]
    exact Nat.beq_refl _
  · rw [hp1, commA_P2 (pA hv (by norm_num)) pT1]
    exact g2
  · rw [hbIdx]; norm_num
  · rw [hbIdx, eqA_P (pA hv (by norm_num)) hB, g4]
    exact Nat.beq_refl _
  · rw [hbIdx, cellReps_get (by norm_num), adjB_eq]
    exact g5

end CertificateChecks.KernelSpor.L2G

end
