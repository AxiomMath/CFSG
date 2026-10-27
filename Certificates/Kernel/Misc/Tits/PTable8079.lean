module

public import Certificates.Kernel.Misc.Tits.JOps8073
public import Certificates.Kernel.Misc.Tits.PVc8079
public import CFSG.Certificates.Kernel.Misc.TitsPiSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.PV

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN CertificateChecks.KernelMisc.TitsJT
open CertificateChecks.KernelMisc.TitsJT.V (X pt onB sJ sJ_rep sJ_mem mem_SJ SJ X_eq pt_eq finPt_coe onB_iff
  Z_rep el_ccF el_cjF hGen_norm cc_norm)

@[expose] noncomputable def piP : Equiv.Perm (Fin 1755) :=
  permOfArr 1755 (unpack 1755 11 CertificateChecks.KernelMisc.TitsPi.P)

theorem piP_rep : Rep 1755 (unpack 1755 11 Pi) piP := (rep_of CertificateChecks.KernelMisc.TitsPi.perm).1

theorem pi_rep : Rep 1755 titsPiArr piP := by
  rw [CFSG.KC.TitsPi.cmpL_sound CertificateChecks.KernelMisc.TitsPi.bind]
  exact piP_rep

structure PiHyp : Prop where
  conjJ : ∀ k < 4, piP * sJ k * piP⁻¹ ∈ titsJ
  sq : piP * piP ∈ titsJ
  conjH : ∀ k < 3, hGen k * piP * (hGen k)⁻¹ * piP⁻¹ ∈ titsJ

variable (hπ : PiHyp)
include hπ

theorem piJ {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsJ) : piP * x * piP⁻¹ ∈ titsJ := by
  have key : ∀ y ∈ Subgroup.closure SJ, piP * y * piP⁻¹ ∈ Subgroup.closure SJ := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨k, hk, rfl⟩ := mem_SJ.1 hs
      rw [V.closure_SJ]
      exact hπ.conjJ k hk
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul a b _ _ ha hb =>
      have e : piP * (a * b) * piP⁻¹ = (piP * a * piP⁻¹) * (piP * b * piP⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : piP * a⁻¹ * piP⁻¹ = (piP * a * piP⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  have hx' : x ∈ Subgroup.closure SJ := by
    rw [V.closure_SJ]
    exact hx
  have h := key x hx'
  rwa [V.closure_SJ] at h

theorem piJ' {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsJ) : piP⁻¹ * x * piP ∈ titsJ := by
  have e : piP⁻¹ * x * piP = (piP * piP)⁻¹ * (piP * x * piP⁻¹) * (piP * piP) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hπ.sq) (piJ hπ hx)) hπ.sq

@[expose] noncomputable def Psub : Subgroup (Equiv.Perm (Fin 1755)) where
  carrier := {x | x ∈ titsJ ∨ x * piP⁻¹ ∈ titsJ}
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · refine Or.inr ?_
      have e : x * y * piP⁻¹ = x * (y * piP⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    · refine Or.inr ?_
      have e : x * y * piP⁻¹ = (x * piP⁻¹) * (piP * y * piP⁻¹) := by group
      rw [e]
      exact mul_mem hx (piJ hπ hy)
    · refine Or.inl ?_
      have e : x * y = (x * piP⁻¹) * (piP * (y * piP⁻¹) * piP⁻¹) * (piP * piP) := by group
      rw [e]
      exact mul_mem (mul_mem hx (piJ hπ hy)) hπ.sq
  one_mem' := Or.inl (one_mem _)
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have e : x⁻¹ * piP⁻¹ = (piP⁻¹ * (x * piP⁻¹)⁻¹ * piP) * (piP * piP)⁻¹ := by group
      rw [e]
      exact mul_mem (piJ' hπ (inv_mem hx)) (inv_mem hπ.sq)

theorem J_le {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsJ) : x ∈ Psub hπ := Or.inl hx

theorem pi_mem : piP ∈ Psub hπ := Or.inr (by rw [mul_inv_cancel]; exact one_mem _)

omit hπ in
@[expose] noncomputable def elP (i : ℕ) : Equiv.Perm (Fin 1755) :=
  if i < 512 then el i else el (i - 512) * piP

omit hπ in
theorem elP_lo {i : ℕ} (hi : i < 512) : elP i = el i := by simp [elP, hi]

omit hπ in
theorem elP_hi {i : ℕ} (hi : ¬ i < 512) : elP i = el (i - 512) * piP := by simp [elP, hi]

omit hπ in
theorem pPel_size : pPel.size = 1024 := by
  rw [pPel]
  exact Array.size_ofFn

omit hπ in
theorem pPel_get {i : ℕ} (hi : i < 1024) :
    pPel[i]! = if i < 512 then jPel[i]! else compA 1755 jPel[i - 512]! titsPiArr := by
  rw [pPel, getElem!_ofFn_of_lt _ hi]

omit hπ in
theorem elP_rep {i : ℕ} (hi : i < 1024) : Rep 1755 pPel[i]! (elP i) := by
  rw [pPel_get hi]
  by_cases h : i < 512
  · simp only [h, ↓reduceIte, elP_lo h]
    exact el_rep h
  · simp only [h, ↓reduceIte, elP_hi h]
    exact rep_compA (el_rep (by omega)) pi_rep

theorem elP_mem {i : ℕ} (hi : i < 1024) : elP i ∈ Psub hπ := by
  by_cases h : i < 512
  · rw [elP_lo h]
    exact J_le hπ (el_mem h)
  · rw [elP_hi h]
    exact Or.inr (by rw [mul_inv_cancel_right]; exact el_mem (by omega))

omit hπ in
theorem blt_lo {i : ℕ} (hi : i < 512) : Nat.blt i 512 = true := by
  rw [Nat.blt_eq]
  exact hi

omit hπ in
theorem blt_hi {i : ℕ} (hi : ¬ i < 512) : Nat.blt i 512 = false := by
  rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
  exact hi

omit hπ in
theorem XP_lo {i p : ℕ} (hi : i < 512) : XP i p = X i p := by
  unfold XP
  rw [blt_lo hi]

omit hπ in
theorem XP_hi {i p : ℕ} (hi : ¬ i < 512) : XP i p = X (i - 512) (pt Pi p) := by
  unfold XP
  rw [blt_hi hi]
  rfl

omit hπ in
theorem XP_eq {i p : ℕ} (hi : i < 1024) (hp : p < 1755) : XP i p = (elP i (finPt 1755 p) : ℕ) := by
  by_cases h : i < 512
  · rw [XP_lo h, elP_lo h, X_eq h hp]
  · rw [XP_hi h, elP_hi h, pt_eq piP_rep hp, X_eq (by omega) (Fin.is_lt _), finPt_coe,
      Equiv.Perm.mul_apply]

omit hπ in
theorem base_lt {p : ℕ} (hp : p ∈ titsJBase) : p < 1755 := by
  simp only [titsJBase, List.mem_cons, List.mem_nil_iff, or_false] at hp
  omega

omit hπ in
theorem tst2 {i : ℕ} (hi : i < 1024) : test2 i (clsP i) = true := allN_spec enumP i hi

omit hπ in
theorem isOneP_hi {i : ℕ} (hi : i < 1024) (h : ¬ i < 512) : isOneP i = false := by
  have t := ((CFSG.KS.bAnd_iff _ _).1 (tst2 hi)).1
  rw [blt_hi h] at t
  change bIf(isOneP i, false, true) = true at t
  cases e : isOneP i
  · rfl
  · rw [e] at t
    exact absurd t (by decide)

omit hπ in
theorem isOneP_iff {i : ℕ} (hi : i < 1024) :
    isOneP i = true ↔ ∀ p ∈ titsJBase, (elP i (finPt 1755 p) : ℕ) = p := by
  unfold isOneP
  rw [onB_iff]
  refine forall₂_congr fun p hp => ?_
  rw [Nat.beq_eq, XP_eq hi (base_lt hp)]

omit hπ in
theorem noFix {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsJ)
    (h : ∀ p ∈ titsJBase, ((g * piP) (finPt 1755 p) : ℕ) = p) : False := by
  obtain ⟨k, hk, rfl⟩ := el_surj hg
  have h1 : ¬ (k + 512 < 512) := by omega
  have e : elP (k + 512) = el k * piP := by rw [elP_hi h1, Nat.add_sub_cancel]
  have := (isOneP_iff (i := k + 512) (by omega)).2 (by rw [e]; exact h)
  rw [isOneP_hi (by omega) h1] at this
  exact Bool.false_ne_true this

omit hπ in
theorem pi_not_mem : piP ∉ titsJ := fun h =>
  noFix (inv_mem h) fun p hp => by
    rw [inv_mul_cancel, Equiv.Perm.one_apply, finPt_val (base_lt hp)]

theorem fix_one {d : Equiv.Perm (Fin 1755)} (hd : d ∈ Psub hπ)
    (h : ∀ p ∈ titsJBase, (d (finPt 1755 p) : ℕ) = p) : d = 1 := by
  rcases hd with hd | hd
  · exact agree hd (one_mem _) fun p hp => by
      rw [h p hp, Equiv.Perm.one_apply, finPt_val (base_lt hp)]
  · exfalso
    exact noFix hd fun p hp => by rw [inv_mul_cancel_right]; exact h p hp

theorem agreeP {g h : Equiv.Perm (Fin 1755)} (hg : g ∈ Psub hπ) (hh : h ∈ Psub hπ)
    (hb : ∀ p ∈ titsJBase, (g (finPt 1755 p) : ℕ) = h (finPt 1755 p)) : g = h := by
  have hd := fix_one hπ (mul_mem (inv_mem hg) hh) fun p hp => by
    have e : h (finPt 1755 p) = g (finPt 1755 p) := Fin.ext (hb p hp).symm
    rw [Equiv.Perm.mul_apply, e, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply,
      finPt_val (base_lt hp)]
  rw [inv_mul_eq_one] at hd
  exact hd

omit hπ in
theorem elP_J_iff {i : ℕ} (hi : i < 1024) : elP i ∈ titsJ ↔ i < 512 := by
  constructor
  · intro h
    by_contra h'
    rw [elP_hi h'] at h
    exact pi_not_mem (by
      have := mul_mem (inv_mem (el_mem (i := i - 512) (by omega))) h
      rwa [inv_mul_cancel_left] at this)
  · intro h
    rw [elP_lo h]
    exact el_mem h

theorem elP_surj {g : Equiv.Perm (Fin 1755)} (hg : g ∈ Psub hπ) : ∃ i < 1024, elP i = g := by
  rcases hg with hg | hg
  · obtain ⟨i, hi, rfl⟩ := el_surj hg
    exact ⟨i, by omega, elP_lo hi⟩
  · obtain ⟨k, hk, e⟩ := el_surj hg
    have h1 : ¬ (k + 512 < 512) := by omega
    refine ⟨k + 512, by omega, ?_⟩
    rw [elP_hi h1, Nat.add_sub_cancel, e, inv_mul_cancel_right]

omit hπ in
theorem elP_inj {i j : ℕ} (hi : i < 1024) (hj : j < 1024) (h : elP i = elP j) : i = j := by
  have hc := (elP_J_iff hi).symm.trans ((iff_of_eq (congrArg (· ∈ titsJ) h)).trans
    (elP_J_iff hj))
  by_cases h1 : i < 512
  · have h2 := hc.1 h1
    rw [elP_lo h1, elP_lo h2] at h
    exact el_inj h1 h2 h
  · have h2 : ¬ j < 512 := fun h2 => h1 (hc.2 h2)
    rw [elP_hi h1, elP_hi h2, mul_left_inj] at h
    have := el_inj (by omega) (by omega) h
    omega

omit hπ in
@[expose] noncomputable def keyP (i : ℕ) : ℕ :=
  jKey4 (pPel[i]!)[5]! (pPel[i]!)[1]! (pPel[i]!)[24]! (pPel[i]!)[12]!

theorem keyP_inj {i j : ℕ} (hi : i < 1024) (hj : j < 1024) (h : keyP i = keyP j) : i = j := by
  have ri := elP_rep hi
  have rj := elP_rep hj
  obtain ⟨e0, e1, e2, e3⟩ := key_inj (ri.lt (by norm_num)) (ri.lt (by norm_num))
    (ri.lt (by norm_num)) (ri.lt (by norm_num)) (rj.lt (by norm_num)) (rj.lt (by norm_num))
    (rj.lt (by norm_num)) (rj.lt (by norm_num)) h
  refine elP_inj hi hj (agreeP hπ (elP_mem hπ hi) (elP_mem hπ hj) fun p hp => ?_)
  simp only [titsJBase, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rw [← rep_base ri _ (by norm_num), ← rep_base rj _ (by norm_num)]; exact e0
  · rw [← rep_base ri _ (by norm_num), ← rep_base rj _ (by norm_num)]; exact e1
  · rw [← rep_base ri _ (by norm_num), ← rep_base rj _ (by norm_num)]; exact e2
  · rw [← rep_base ri _ (by norm_num), ← rep_base rj _ (by norm_num)]; exact e3

theorem idxP_key {i : ℕ} (hi : i < 1024) : pIdxMap.getD (keyP i) 0 = i := by
  have e := foldl_insert keyP 1024 (fun i hi j hj h => keyP_inj hπ hi hj h) i hi
  rw [pIdxMap]
  change ((List.range 1024).foldl (fun m i => m.insert (keyP i) i) (∅ : Std.HashMap ℕ ℕ)).getD
    (keyP i) 0 = i
  rw [Std.HashMap.getD_eq_getD_getElem?, e]
  rfl

theorem pIdx_of {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) (hg : g ∈ Psub hπ) :
    ∃ i < 1024, elP i = g ∧ pIdx a = i := by
  obtain ⟨i, hi, rfl⟩ := elP_surj hπ hg
  refine ⟨i, hi, rfl, ?_⟩
  have ri := elP_rep hi
  have e : ∀ p < 1755, a[p]! = (pPel[i]!)[p]! := fun p hp => by
    rw [rep_base ha p hp, rep_base ri p hp]
  rw [pIdx, pIdx4, e 5 (by norm_num), e 1 (by norm_num), e 24 (by norm_num), e 12 (by norm_num)]
  exact idxP_key hπ hi

theorem pIdx4_of {g : Equiv.Perm (Fin 1755)} (hg : g ∈ Psub hπ) :
    ∃ i < 1024, elP i = g ∧ pIdx4 (g (finPt 1755 5)) (g (finPt 1755 1)) (g (finPt 1755 24))
      (g (finPt 1755 12)) = i := by
  obtain ⟨i, hi, rfl⟩ := elP_surj hπ hg
  refine ⟨i, hi, rfl, ?_⟩
  have ri := elP_rep hi
  rw [pIdx4, ← rep_base ri 5 (by norm_num), ← rep_base ri 1 (by norm_num),
    ← rep_base ri 24 (by norm_num), ← rep_base ri 12 (by norm_num)]
  exact idxP_key hπ hi

omit hπ in
@[expose] noncomputable def genP (k : ℕ) : Equiv.Perm (Fin 1755) := if k < 3 then hGen k else piP

omit hπ in
theorem pGenArrs_get {k : ℕ} (hk : k < 4) : Rep 1755 pGenArrs[k]! (genP k) := by
  have hs : jGenArrs.size = 3 := gens_size
  have hs' : pGenArrs.size = 4 := by rw [pGenArrs, Array.size_push, hs]
  rw [getElem!_pos _ k (by omega)]
  by_cases h : k < 3
  · simp only [pGenArrs, Array.getElem_push_lt (by omega : k < jGenArrs.size), genP, h, ↓reduceIte]
    have := (hGenArr h).2
    rwa [getElem!_pos _ k (by omega)] at this
  · have e : k = 3 := by omega
    subst e
    simp only [pGenArrs, genP, h, ↓reduceIte]
    rw [Array.getElem_push]
    simp only [hs, lt_self_iff_false, ↓reduceDIte]
    exact pi_rep

omit hπ in
theorem pGenInv_get {k : ℕ} (hk : k < 4) : pGenInvArrs[k]! = invCand 1755 pGenArrs[k]! := by
  have hs' : pGenArrs.size = 4 := by rw [pGenArrs, Array.size_push, gens_size]
  rw [pGenInvArrs, getElem!_map_of_lt (by rw [hs']; exact hk)]

theorem hGen_normP {k : ℕ} (hk : k < 3) {x : Equiv.Perm (Fin 1755)} (hx : x ∈ Psub hπ) :
    hGen k * x * (hGen k)⁻¹ ∈ Psub hπ := by
  rcases hx with hx | hx
  · exact J_le hπ (hGen_norm hk hx)
  · refine Or.inr ?_
    have e : hGen k * x * (hGen k)⁻¹ * piP⁻¹ =
        (hGen k * (x * piP⁻¹) * (hGen k)⁻¹) * (hGen k * piP * (hGen k)⁻¹ * piP⁻¹) := by group
    rw [e]
    exact mul_mem (hGen_norm hk hx) (hπ.conjH k hk)

theorem pi_normP {x : Equiv.Perm (Fin 1755)} (hx : x ∈ Psub hπ) : piP * x * piP⁻¹ ∈ Psub hπ :=
  mul_mem (mul_mem (pi_mem hπ) hx) (inv_mem (pi_mem hπ))

theorem genP_norm {k : ℕ} (_hk : k < 4) {x : Equiv.Perm (Fin 1755)} (hx : x ∈ Psub hπ) :
    genP k * x * (genP k)⁻¹ ∈ Psub hπ := by
  by_cases h : k < 3
  · simp only [genP, h, ↓reduceIte]
    exact hGen_normP hπ h hx
  · simp only [genP, h, ↓reduceIte]
    exact pi_normP hπ hx

omit hπ in
theorem c0_eq : c0 = hGen 0 * hGen 1 * hGen 2 := by
  have e : ([3, 4, 13] : List ℤ) = [3] ++ [4] ++ [13] := rfl
  have e0 : titsHWords[0]! = [3] := by decide
  have e1 : titsHWords[1]! = [4] := by decide
  have e2 : titsHWords[2]! = [13] := by decide
  rw [c0, e, wordIn_append, wordIn_append, hGen, hGen, hGen, e0, e1, e2]

theorem cc_normP {x : Equiv.Perm (Fin 1755)} (hx : x ∈ Psub hπ) : cc * x * cc⁻¹ ∈ Psub hπ := by
  have h1 : ∀ y ∈ Psub hπ, c0 * y * c0⁻¹ ∈ Psub hπ := fun y hy => by
    have e : c0 * y * c0⁻¹ = hGen 0 * (hGen 1 * (hGen 2 * y * (hGen 2)⁻¹) * (hGen 1)⁻¹) *
        (hGen 0)⁻¹ := by rw [c0_eq]; group
    rw [e]
    exact hGen_normP hπ (by norm_num) (hGen_normP hπ (by norm_num)
      (hGen_normP hπ (by norm_num) hy))
  have e : cc * x * cc⁻¹ = c0 * (c0 * x * c0⁻¹) * c0⁻¹ := by rw [cc]; group
  rw [e]
  exact h1 _ (h1 x hx)

omit hπ in
theorem prodP_pt {i j : ℕ} (hi : i < 1024) (hj : j < 1024) {p : ℕ} (hp : p < 1755) :
    (pPel[i]!)[(pPel[j]!)[p]!]! = ((elP i * elP j) (finPt 1755 p) : ℕ) := by
  rw [rep_base (elP_rep hj) p hp, (elP_rep hi) (elP j (finPt 1755 p)), Equiv.Perm.mul_apply]

theorem mulTP {i j : ℕ} (hi : i < 1024) (hj : j < 1024) :
    (pMulT[i]!)[j]! < 1024 ∧ elP (pMulT[i]!)[j]! = elP i * elP j := by
  obtain ⟨k, hk, ek, ik⟩ := pIdx4_of hπ (mul_mem (elP_mem hπ hi) (elP_mem hπ hj))
  have e : (pMulT[i]!)[j]! = k := by
    rw [pMulT, getElem!_ofFn_of_lt _ hi, getElem!_ofFn_of_lt _ hj]
    simp only [Fin.getElem!_fin]
    rw [prodP_pt hi hj (p := 5) (by norm_num), prodP_pt hi hj (p := 1) (by norm_num),
      prodP_pt hi hj (p := 24) (by norm_num), prodP_pt hi hj (p := 12) (by norm_num)]
    exact ik
  rw [e]
  exact ⟨hk, ek⟩

theorem invTP {i : ℕ} (hi : i < 1024) : pInvT[i]! < 1024 ∧ elP pInvT[i]! = (elP i)⁻¹ := by
  obtain ⟨k, hk, ek, ik⟩ := pIdx_of hπ (rep_invCandJ (elP_rep hi)) (inv_mem (elP_mem hπ hi))
  have e : pInvT[i]! = k := by
    rw [pInvT, getElem!_ofFn_of_lt _ hi]
    exact ik
  rw [e]
  exact ⟨hk, ek⟩

theorem oneTP : pOneI < 1024 ∧ elP pOneI = 1 := by
  obtain ⟨k, hk, ek, ik⟩ := pIdx_of hπ rep_idA (one_mem _)
  have e : pOneI = k := ik
  rw [e]
  exact ⟨hk, ek⟩

theorem zTP : pZI < 1024 ∧ elP pZI = titsZ := by
  obtain ⟨k, hk, ek, ik⟩ := pIdx_of hπ (titsZ_rep : Rep 1755 jZArr titsZ) (J_le hπ z_mem)
  have e : pZI = k := ik
  rw [e]
  exact ⟨hk, ek⟩

theorem ccTP {i : ℕ} (hi : i < 1024) : pCcT[i]! < 1024 ∧ elP pCcT[i]! = cc * elP i * cc⁻¹ := by
  have r := rep_compA (rep_compA cFacts.2.2.1 (elP_rep hi)) (rep_invCandJ cFacts.2.2.1)
  obtain ⟨k, hk, ek, ik⟩ := pIdx_of hπ r (cc_normP hπ (elP_mem hπ hi))
  have e : pCcT[i]! = k := by
    rw [pCcT, getElem!_ofFn_of_lt _ hi]
    exact ik
  rw [e]
  exact ⟨hk, ek⟩

theorem cjTP {k i : ℕ} (hk : k < 4) (hi : i < 1024) :
    (pCjT[k]!)[i]! < 1024 ∧ elP (pCjT[k]!)[i]! = genP k * elP i * (genP k)⁻¹ := by
  have ha := pGenArrs_get hk
  have r := rep_compA (rep_compA ha (elP_rep hi)) (rep_invCandJ ha)
  obtain ⟨m, hm, em, im⟩ := pIdx_of hπ r (genP_norm hπ hk (elP_mem hπ hi))
  have e : (pCjT[k]!)[i]! = m := by
    rw [pCjT, getElem!_ofFn_of_lt _ hk, getElem!_ofFn_of_lt _ hi]
    simp only [Fin.getElem!_fin]
    rw [pGenInv_get hk]
    exact im
  rw [e]
  exact ⟨hm, em⟩

theorem pmul_ok : (allLt 1024 fun i => allLt 1024 fun j => decide ((pMulT[i]!)[j]! < 1024) &&
    titsJBase.all fun p => (pPel[(pMulT[i]!)[j]!]!)[p]! == (pPel[i]!)[(pPel[j]!)[p]!]!) =
    true := by
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
  obtain ⟨hk, ek⟩ := mulTP hπ hi hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  refine ⟨hk, fun p hp => ?_⟩
  have hp' := base_lt hp
  rw [prodP_pt hi hj hp', rep_base (elP_rep hk) p hp', ek]

theorem pinv_ok : (allLt 1024 fun i => decide (pInvT[i]! < 1024) &&
    isInvA 1755 pPel[i]! (invCand 1755 pPel[i]!) &&
    eqA 1755 (invCand 1755 pPel[i]!) pPel[pInvT[i]!]!) = true := by
  refine allLt_iff.2 fun i hi => ?_
  have ri := elP_rep hi
  obtain ⟨hk, ek⟩ := invTP hπ hi
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hk, isInvA_invCand ri⟩, (eqA_iff (rep_invCandJ ri) (elP_rep hk)).2 ek.symm⟩

theorem pone_ok : pOneI < 1024 ∧ eqA 1755 pPel[pOneI]! (idA 1755) = true :=
  ⟨(oneTP hπ).1, (eqA_iff (elP_rep (oneTP hπ).1) rep_idA).2 (oneTP hπ).2⟩

theorem pz_ok : pZI < 1024 ∧ eqA 1755 pPel[pZI]! jZArr = true :=
  ⟨(zTP hπ).1, (eqA_iff (elP_rep (zTP hπ).1) (titsZ_rep : Rep 1755 jZArr titsZ)).2 (zTP hπ).2⟩

theorem pdist_ok : (allLt 1024 fun i => allLt 1024 fun j => i == j ||
    titsJBase.any fun p => (pPel[i]!)[p]! != (pPel[j]!)[p]!) = true := by
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
  by_cases hij : i = j
  · rw [hij, beq_self_eq_true, Bool.true_or]
  · simp only [Bool.or_eq_true, beq_iff_eq, hij, false_or, List.any_eq_true, bne_iff_ne, ne_eq]
    by_contra hc
    push Not at hc
    refine hij (elP_inj hi hj (agreeP hπ (elP_mem hπ hi) (elP_mem hπ hj) fun p hp => ?_))
    rw [← rep_base (elP_rep hi) p (base_lt hp), ← rep_base (elP_rep hj) p (base_lt hp)]
    exact hc p hp

omit hπ in
theorem pgenInv_ok : (allLt 4 fun k => isInvA 1755 pGenArrs[k]! pGenInvArrs[k]!) = true :=
  allLt_iff.2 fun k hk => by
    rw [pGenInv_get hk]
    exact isInvA_invCand (pGenArrs_get hk)

theorem pcj_ok : (allLt 4 fun k => allLt 1024 fun i => decide ((pCjT[k]!)[i]! < 1024) &&
    eqA 1755 (compA 1755 (compA 1755 pGenArrs[k]! pPel[i]!) pGenInvArrs[k]!)
      pPel[(pCjT[k]!)[i]!]!) = true := by
  refine allLt_iff.2 fun k hk => allLt_iff.2 fun i hi => ?_
  obtain ⟨hm, em⟩ := cjTP hπ hk hi
  have ha := pGenArrs_get hk
  rw [pGenInv_get hk]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hm, (eqA_iff (rep_compA (rep_compA ha (elP_rep hi)) (rep_invCandJ ha)) (elP_rep hm)).2
    em.symm⟩

theorem pcc_ok : (allLt 1024 fun i => decide (pCcT[i]! < 1024) &&
    eqA 1755 (compA 1755 (compA 1755 jCArr pPel[i]!) jCInv) pPel[pCcT[i]!]!) = true := by
  refine allLt_iff.2 fun i hi => ?_
  obtain ⟨hm, em⟩ := ccTP hπ hi
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hm, (eqA_iff (rep_compA (rep_compA cFacts.2.2.1 (elP_rep hi)) (rep_invCandJ cFacts.2.2.1))
    (elP_rep hm)).2 em.symm⟩

theorem ptable_facts :
    pPel.size = 1024 ∧
    (allLt 1024 fun i => allLt 1024 fun j => decide ((pMulT[i]!)[j]! < 1024) &&
      titsJBase.all fun p => (pPel[(pMulT[i]!)[j]!]!)[p]! == (pPel[i]!)[(pPel[j]!)[p]!]!) = true ∧
    (allLt 1024 fun i => decide (pInvT[i]! < 1024) &&
      isInvA 1755 pPel[i]! (invCand 1755 pPel[i]!) &&
      eqA 1755 (invCand 1755 pPel[i]!) pPel[pInvT[i]!]!) = true ∧
    pOneI < 1024 ∧ eqA 1755 pPel[pOneI]! (idA 1755) = true ∧
    pZI < 1024 ∧ eqA 1755 pPel[pZI]! jZArr = true ∧
    (allLt 1024 fun i => allLt 1024 fun j => i == j ||
      titsJBase.any fun p => (pPel[i]!)[p]! != (pPel[j]!)[p]!) = true ∧
    (allLt 4 fun k => isInvA 1755 pGenArrs[k]! pGenInvArrs[k]!) = true ∧
    (allLt 4 fun k => allLt 1024 fun i => decide ((pCjT[k]!)[i]! < 1024) &&
      eqA 1755 (compA 1755 (compA 1755 pGenArrs[k]! pPel[i]!) pGenInvArrs[k]!)
        pPel[(pCjT[k]!)[i]!]!) = true ∧
    (allLt 1024 fun i => decide (pCcT[i]! < 1024) &&
      eqA 1755 (compA 1755 (compA 1755 jCArr pPel[i]!) jCInv) pPel[pCcT[i]!]!) = true :=
  ⟨pPel_size, pmul_ok hπ, pinv_ok hπ, (pone_ok hπ).1, (pone_ok hπ).2, (pz_ok hπ).1,
    (pz_ok hπ).2, pdist_ok hπ, pgenInv_ok, pcj_ok hπ, pcc_ok hπ⟩

end CertificateChecks.KernelMisc.TitsJT.PV

end
