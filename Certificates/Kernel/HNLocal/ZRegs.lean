module

public import Certificates.Kernel.HNLocal.Census
public import Certificates.Kernel.HNLocal.ZData
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporHNInputs
import Certificates.Kernel.HNLocal.Checks.ZR
import Certificates.Kernel.HNLocal.Checks.ZW0
import Certificates.Kernel.HNLocal.Checks.ZW1
import Certificates.Kernel.HN3166.Ord
import Certificates.Kernel.HN3166.Seed
import Certificates.Kernel.VecCert.WordProg
import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNLocalZ

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNMult CFSG.KD.HNLocalZ CFSG.Sporadic.F5
open CFSG.Sporadic.HN.LocalK CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CertificateChecks.KernelHNLocal

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

local notation "OM" => ordMat 5 (CFSG.Sporadic.F5.Native.F5Data.d CFSG.Sporadic.HN.Native.hnData) 13 1729

local notation "MUL" => CFSG.KD.HNLocal.mul

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

@[expose] noncomputable def lm (c : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) :=
  OM (letM RZ 86 (letC c))

@[expose] noncomputable def Mr (g : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) :=
  OM (RZ (g + 1))

@[expose] noncomputable def Mi (g : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) :=
  OM (RZ (87 + g))

theorem lm_eq (c : ℕ) : lm c = if c % 2 = 1 then Mr (c / 2) else Mi (c / 2) := by
  unfold lm Mr Mi
  rw [CertificateChecks.KernelWP.letC_div]
  by_cases h : c % 2 = 1
  · simp only [h, decide_true, if_true]
    rfl
  · simp only [h, decide_false, if_false]
    change OM (RZ (Nat.add (Nat.succ 86) (c / 2))) = _
    rfl

theorem sound {rels : List (List (ℕ × Bool))} (hb : relsBounded rels 86 = true)
    (hr : ∀ r < lenRels rels, relOK RZ MUL rels 86 CFSG.KD.OrdHN.ONE r = true ∨
      ∃ s < r, relDupOK rels s r = true) :
    (∀ g < 86, ordMat 5 133 13 1729 (RZ (g + 1)) * ordMat 5 133 13 1729 (RZ (86 + 1 + g)) = 1) ∧
      ∀ v ∈ rels, (v.map fun x => ordMat 5 133 13 1729 (letM RZ 86 x)).prod = 1 :=
  rels_sound (p := 5) (d := 133) (w := 13) (S := 1729) (T := 9) (L := CFSG.KD.OrdHN.L)
    (H := CFSG.KD.OrdHN.H) (CM := CFSG.KD.OrdHN.CM) (RM := CFSG.KD.OrdHN.RM)
    (ONE := CFSG.KD.OrdHN.ONE) (LV := CFSG.KD.OrdHN.LV) (HV := CFSG.KD.OrdHN.HV)
    (nb := 229957) (Lg := 86) (RB := RZ) CFSG.KD.OrdHN.consts rfl CFSG.KD.HNLocalZ.roots
    CFSG.KD.HNLocalZ.invs hb hr

theorem pair (g : ℕ) (hg : g < 86) : Mr g * Mi g = 1 := by
  have h := (sound (rels := []) rfl (fun r hr => absurd hr (Nat.not_lt_zero r))).1 g hg
  have e : 86 + 1 + g = 87 + g := by omega
  rw [e] at h
  exact h

theorem relW_one {w : List ℕ} (h : relW RZ MUL 86 CFSG.KD.OrdHN.ONE w = true) :
    (w.map lm).prod = 1 := by
  obtain ⟨hb, hr⟩ := andB_true h
  have hs := (sound hb (fun r hr' => by
      have h1 : r = 0 := by
        have : lenRels (List.cons (decL w) List.nil) = 1 := rfl
        omega
      subst h1
      exact Or.inl hr)).2 (decL w) List.mem_cons_self
  rw [decL_eq, List.map_map] at hs
  exact hs

theorem range_spec {lo : ℕ} :
    ∀ n, relWRange RZ MUL 86 CFSG.KD.OrdHN.ONE WZL lo n = true →
      ∀ k < n, relW RZ MUL 86 CFSG.KD.OrdHN.ONE (WZL (lo + k)) = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact range_spec n h1 k hk
    · exact h2

theorem zRel_ok {c : ℕ} (hc : c < 8) : zRel c = true := by
  interval_cases c
  · exact zRel0
  · exact zRel1
  · exact zRel2
  · exact zRel3
  · exact zRel4
  · exact zRel5
  · exact zRel6
  · exact zRel7

theorem word_one {k : ℕ} (hk : k < 127) : ((WZL k).map lm).prod = 1 := by
  have hz : relWRange RZ MUL 86 CFSG.KD.OrdHN.ONE WZL (16 * (k / 16))
      (min 16 (127 - 16 * (k / 16))) = true := zRel_ok (c := k / 16) (by omega)
  have h := range_spec _ hz (k % 16) (by omega)
  rw [Nat.div_add_mod] at h
  exact relW_one h

theorem mul_comm_of_one {d : ℕ} {A B : Matrix (Fin d) (Fin d) (ZMod 5)} (h : A * B = 1) :
    B * A = 1 :=
  mul_eq_one_comm.mp h

theorem word_root {k g : ℕ} (hk : k < 127) (hg : g < 86) {u : List ℕ} (hu : WZL k = u ++ [2 * g]) :
    (u.map lm).prod = Mr g := by
  have h := word_one hk
  rw [hu, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
    lm_eq, if_neg (by omega : ¬ 2 * g % 2 = 1), Nat.mul_div_cancel_left g (by norm_num)] at h
  have h2 : Mi g * Mr g = 1 := mul_comm_of_one (pair g hg)
  calc (u.map lm).prod = (u.map lm).prod * (Mi g * Mr g) := by rw [h2, mul_one]
    _ = Mr g := by rw [← mul_assoc, h, one_mul]

theorem mat_inv_of {x : J Dt} {g : ℕ} (hg : g < 86) (hx : mat Dt x = Mr g) :
    mat Dt x⁻¹ = Mi g := by
  have h1 : mat Dt x⁻¹ * mat Dt x = 1 := by
    rw [mat_eq, mat_eq, ← map_mul, inv_mul_cancel, map_one]
  calc mat Dt x⁻¹ = mat Dt x⁻¹ * (Mr g * Mi g) := by rw [pair g hg, mul_one]
    _ = Mi g := by rw [← mul_assoc, ← hx, h1, one_mul]

theorem mat_a : mat Dt (a Dt) = Mr 0 := by
  rw [mat_a' CertificateChecks.KernelHN.det_mA, CertificateChecks.KernelHN.o_mA]
  exact congrArg OM (Nat.eq_of_beq_eq_true CFSG.KD.HNLocalZ.ra).symm

theorem mat_b : mat Dt (b Dt) = Mr 1 := by
  rw [mat_b' CertificateChecks.KernelHN.det_mB, CertificateChecks.KernelHN.o_mB]
  exact congrArg OM (Nat.eq_of_beq_eq_true CFSG.KD.HNLocalZ.rb).symm

theorem tie_w : ∀ j < 63, 2 ≤ j →
    WZL (j - 2) = CFSG.Sporadic.HN.Local.Native.invWords[j]!.map slpCode ++ [2 * j] := by
  decide +kernel

theorem bnd_w : ∀ j < 63, ∀ z ∈ CFSG.Sporadic.HN.Local.Native.invWords[j]!,
    (z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∨ (3 ≤ z.natAbs ∧ z.natAbs - 3 < j) := by
  decide +kernel

theorem mat_wG : ∀ j < 63, mat Dt (wG j) = Mr j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · interval_cases j
      · rw [wG0, mat_a]
      · rw [wG1, mat_b]
    · have hw := word_root (k := j - 2) (by omega) (by omega) (tie_w j hj h2)
      rw [← hw]
      change mat Dt (slpG (genG Dt) CFSG.Sporadic.HN.Local.Native.invWords j) = _
      rw [slpG_eq, mat_wordG, List.map_map]
      congr 1
      refine List.map_congr_left fun z hz => ?_
      beta_reduce
      change _ = lm (slpCode z)
      rw [lm_eq]
      have hai := mat_inv_of (x := a Dt) (g := 0) (by norm_num) mat_a
      have hbi := mat_inv_of (x := b Dt) (g := 1) (by norm_num) mat_b
      rcases bnd_w j hj z hz with (rfl | rfl | rfl | rfl) | ⟨h3, h4⟩
      · simp [genG, slpCode, mat_a]
      · simp [genG, slpCode, hai]
      · simp [genG, slpCode, mat_b]
      · simp [genG, slpCode, hbi]
      · have hz2 : ¬ z.natAbs ≤ 2 := by omega
        rw [if_neg hz2, if_pos h4]
        have hk : slpCode z / 2 = z.natAbs - 3 := by
          unfold slpCode
          rw [if_neg hz2]
          split_ifs <;> omega
        rw [hk]
        have hg' := ih (z.natAbs - 3) h4 (by omega)
        by_cases hp : 0 < z
        · have hc : slpCode z % 2 = 1 := by
            unfold slpCode
            rw [if_neg hz2, if_pos hp]
            omega
          rw [if_pos hp, if_pos hc]
          exact hg'
        · have hc : ¬ slpCode z % 2 = 1 := by
            unfold slpCode
            rw [if_neg hz2, if_neg hp]
            omega
          rw [if_neg hp, if_neg hc]
          exact mat_inv_of (by omega) hg'

theorem pc_el (k : ℕ) (hk : k < 14) :
    ∃ x : J Dt, x ∈ QJ ∧ mat Dt x = OM (CFSG.KD.HNLocal.PC k) := by
  obtain ⟨-, g, hgJ, hg⟩ := CFSG.KS.J4Hub.pc_reg (nb := nat_lit 229957) rfl CFSG.KD.OrdHN.consts
    CertificateChecks.KernelHN.o_regs CFSG.KD.OrdHN.s2_pr hk
  refine ⟨⟨g, hgJ⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact CFSG.KS.J4Hub.mem_pcSub (Nat.zero_le k) hk hg
  · change ((g : GL (Fin 133) (ZMod 5)) : Matrix (Fin 133) (Fin 133) (ZMod 5)) = _
    rw [hg]
    unfold CFSG.KS.J4Hub.pcMat
    rw [PC_eq k hk]
    rfl

@[expose] noncomputable def pcJ (k : ℕ) : J Dt := if h : k < 14 then (pc_el k h).choose else 1

theorem pcJ_mem (k : ℕ) : pcJ k ∈ QJ := by
  unfold pcJ
  split_ifs with h
  · exact (pc_el k h).choose_spec.1
  · exact one_mem _

theorem mat_pcJ {k : ℕ} (hk : k < 14) : mat Dt (pcJ k) = OM (CFSG.KD.HNLocal.PC k) := by
  unfold pcJ
  rw [dif_pos hk]
  exact (pc_el k hk).choose_spec.2

@[expose] noncomputable def nfJ (e : ℕ → ℕ) : J Dt :=
  ((List.range' 0 14).map fun i => pcJ i ^ e i).prod

theorem nfJ_mem (e : ℕ → ℕ) : nfJ e ∈ QJ := by
  unfold nfJ
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  exact pow_mem (pcJ_mem i) _

theorem mat_nfJ (e : ℕ → ℕ) : mat Dt (nfJ e) = CFSG.KS.HNLocal.nfE CFSG.KD.HNLocal.PC 14 e := by
  unfold nfJ CFSG.KS.HNLocal.nfE
  rw [mat_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range'] at hi
  change mat Dt (pcJ i ^ e i) = _
  rw [CertificateChecks.KernelHN.mat_pow', mat_pcJ (by omega)]
  rfl

theorem nfJ_congr {e e' : ℕ → ℕ} (h : ∀ i < 14, e i = e' i) : nfJ e = nfJ e' := by
  unfold nfJ
  refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range'] at hi
  rw [h i (by omega)]

theorem nf_surj {y : J Dt} (hy : y ∈ QJ) : ∃ e : ℕ → ℕ, (∀ k, e k < 2) ∧ y = nfJ e := by
  obtain ⟨e, he, hge⟩ := Q2_normal.2 y.1 (Subgroup.mem_subgroupOf.1 hy)
  refine ⟨e, he, mat_injective Dt ?_⟩
  rw [mat_nfJ, ← nfProd_eq]
  exact hge

@[expose] noncomputable def nfV (v : Fin 14 → Fin 2) : QJ :=
  ⟨nfJ fun i => if h : i < 14 then (v ⟨i, h⟩).val else 0, nfJ_mem _⟩

theorem nfV_bij : Function.Bijective nfV := by
  refine Function.Surjective.bijective_of_nat_card_le (fun y => ?_) ?_
  · obtain ⟨e, he, hy⟩ := nf_surj y.2
    refine ⟨fun i => ⟨e i, he i⟩, Subtype.ext ?_⟩
    have h1 : nfJ (fun j => if hj : j < 14 then (⟨e j, he j⟩ : Fin 2).val else 0) = nfJ e :=
      nfJ_congr fun j hj => dif_pos hj
    rw [hy]
    exact h1
  · rw [card_QJ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem nf_inj {e e' : ℕ → ℕ} (he : ∀ i, e i < 2) (he' : ∀ i, e' i < 2) (h : nfJ e = nfJ e') :
    ∀ i < 14, e i = e' i := by
  intro i hi
  have hv : (fun j : Fin 14 => (⟨e j, he j⟩ : Fin 2)) = fun j => ⟨e' j, he' j⟩ := by
    have h1 : nfJ (fun j => if hj : j < 14 then (⟨e j, he j⟩ : Fin 2).val else 0) = nfJ e :=
      nfJ_congr fun j hj => dif_pos hj
    have h2 : nfJ (fun j => if hj : j < 14 then (⟨e' j, he' j⟩ : Fin 2).val else 0) = nfJ e' :=
      nfJ_congr fun j hj => dif_pos hj
    exact nfV_bij.1 (Subtype.ext (h1.trans (h.trans h2.symm)))
  exact congrArg Fin.val (congrFun hv ⟨i, hi⟩)

@[expose] def Rep (g : ℕ) : Prop := ∃ x : J Dt, mat Dt x = Mr g

theorem rep_word : ∀ u : List ℕ, (∀ c ∈ u, c / 2 < 86 ∧ Rep (c / 2)) →
    ∃ x : J Dt, mat Dt x = (u.map lm).prod
  | [], _ => ⟨1, by simp [CertificateChecks.KernelHN.mat_one']⟩
  | c :: u, h => by
    obtain ⟨xu, hxu⟩ := rep_word u fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    obtain ⟨hc, y, hy⟩ := h c List.mem_cons_self
    have hl : ∃ x : J Dt, mat Dt x = lm c := by
      rw [lm_eq]
      split_ifs
      · exact ⟨y, hy⟩
      · exact ⟨y⁻¹, mat_inv_of hc hy⟩
    obtain ⟨x, hx⟩ := hl
    refine ⟨x * xu, ?_⟩
    rw [CertificateChecks.KernelHN.mat_mul', hx, hxu, List.map_cons, List.prod_cons]

theorem rep_last {k g : ℕ} (hk : k < 127) (hg : g < 86) {u : List ℕ} (hu : WZL k = u ++ [2 * g])
    (h : ∀ c ∈ u, c / 2 < 86 ∧ Rep (c / 2)) : Rep g := by
  obtain ⟨x, hx⟩ := rep_word u h
  exact ⟨x, hx.trans (word_root hk hg hu)⟩

theorem rep_first {k g : ℕ} (hk : k < 127) {u : List ℕ} (hu : WZL k = (2 * g + 1) :: u)
    (h : ∀ c ∈ u, c / 2 < 86 ∧ Rep (c / 2)) : Rep g := by
  obtain ⟨x, hx⟩ := rep_word u h
  have h1 := word_one hk
  have e : (2 * g + 1) / 2 = g := by omega
  rw [hu, List.map_cons, List.prod_cons, lm_eq, if_pos (by omega), e, ← hx] at h1
  have h2 : mat Dt x * mat Dt x⁻¹ = 1 := by
    rw [← CertificateChecks.KernelHN.mat_mul', mul_inv_cancel, CertificateChecks.KernelHN.mat_one']
  refine ⟨x⁻¹, ?_⟩
  calc mat Dt x⁻¹ = (Mr g * mat Dt x) * mat Dt x⁻¹ := by rw [h1, one_mul]
    _ = Mr g := by rw [mul_assoc, h2, mul_one]

end CertificateChecks.KernelHNLocalZ

end
