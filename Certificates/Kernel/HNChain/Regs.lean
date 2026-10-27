module

public import CFSG.Sporadic.HN.Commutant
public import CFSG.Sporadic.HNSchreier.LevelInputs
public import Certificates.Kernel.HNChain.Data
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import Certificates.Kernel.HNChain.Checks.R
import Certificates.Kernel.HN3166.Ord
import Certificates.Kernel.HN3166.Seed
import Certificates.Kernel.VecCert.WordProg
import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNChain

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNMult CFSG.KD.HNChain CFSG.Sporadic.F5

local notation "Ds" => CFSG.Sporadic.HNSchreier.Native.hnsData

local notation "OMs" => ordMat 5 (CFSG.Sporadic.F5.Native.F5Data.d CFSG.Sporadic.HNSchreier.Native.hnsData) 13 1729

local notation "MUL" => CFSG.KD.HNLocal.mul

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem decL_eq (w : List ℕ) : decL w = w.map letC := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change List.cons (letC c) (decL w) = _
    rw [ih, List.map_cons]

@[expose] noncomputable def lm (c : ℕ) : Matrix (Fin (Ds).d) (Fin (Ds).d) (ZMod 5) :=
  OMs (letM RB 18 (letC c))

@[expose] noncomputable def Mr (g : ℕ) : Matrix (Fin (Ds).d) (Fin (Ds).d) (ZMod 5) := OMs (RB (g + 1))

@[expose] noncomputable def Mi (g : ℕ) : Matrix (Fin (Ds).d) (Fin (Ds).d) (ZMod 5) := OMs (RB (19 + g))

theorem lm_eq (c : ℕ) : lm c = if c % 2 = 1 then Mr (c / 2) else Mi (c / 2) := by
  unfold lm Mr Mi
  rw [CertificateChecks.KernelWP.letC_div]
  by_cases h : c % 2 = 1
  · simp only [h, decide_true, if_true]
    rfl
  · simp only [h, decide_false, if_false]
    change OMs (RB (Nat.add (Nat.succ 18) (c / 2))) = _
    rfl

theorem sound {rels : List (List (ℕ × Bool))} (hb : relsBounded rels 18 = true)
    (hr : ∀ r < lenRels rels, relOK RB MUL rels 18 CFSG.KD.OrdHN.ONE r = true ∨
      ∃ s < r, relDupOK rels s r = true) :
    (∀ g < 18, ordMat 5 133 13 1729 (RB (g + 1)) * ordMat 5 133 13 1729 (RB (18 + 1 + g)) = 1) ∧
      ∀ v ∈ rels, (v.map fun x => ordMat 5 133 13 1729 (letM RB 18 x)).prod = 1 :=
  rels_sound (p := 5) (d := 133) (w := 13) (S := 1729) (T := 9) (L := CFSG.KD.OrdHN.L)
    (H := CFSG.KD.OrdHN.H) (CM := CFSG.KD.OrdHN.CM) (RM := CFSG.KD.OrdHN.RM)
    (ONE := CFSG.KD.OrdHN.ONE) (LV := CFSG.KD.OrdHN.LV) (HV := CFSG.KD.OrdHN.HV)
    (nb := 229957) (Lg := 18) (RB := RB) CFSG.KD.OrdHN.consts rfl roots invs hb hr

theorem mul_comm_of_one {d : ℕ} {A B : Matrix (Fin d) (Fin d) (ZMod 5)} (h : A * B = 1) :
    B * A = 1 :=
  mul_eq_one_comm.mp h

theorem pair (g : ℕ) (hg : g < 18) : Mr g * Mi g = 1 := by
  have h := (sound (rels := []) rfl (fun r hr => absurd hr (Nat.not_lt_zero r))).1 g hg
  have e : 18 + 1 + g = 19 + g := by omega
  rw [e] at h
  exact h

theorem relW_one {w : List ℕ} (h : relW RB MUL 18 CFSG.KD.OrdHN.ONE w = true) :
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
    ∀ n, relWRange RB MUL 18 CFSG.KD.OrdHN.ONE WDL lo n = true →
      ∀ k < n, relW RB MUL 18 CFSG.KD.OrdHN.ONE (WDL (lo + k)) = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact range_spec n h1 k hk
    · exact h2

theorem word_one {k : ℕ} (hk : k < 16) : ((WDL k).map lm).prod = 1 := by
  have h := range_spec 16 rws k hk
  rw [Nat.zero_add] at h
  exact relW_one h

theorem word_root {k g : ℕ} (hk : k < 16) (hg : g < 18) {u : List ℕ} (hu : WDL k = u ++ [2 * g]) :
    (u.map lm).prod = Mr g := by
  have h := word_one hk
  rw [hu, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
    lm_eq, if_neg (by omega : ¬ 2 * g % 2 = 1), Nat.mul_div_cancel_left g (by norm_num)] at h
  have h2 : Mi g * Mr g = 1 := mul_comm_of_one (pair g hg)
  calc (u.map lm).prod = (u.map lm).prod * (Mi g * Mr g) := by rw [h2, mul_one]
    _ = Mr g := by rw [← mul_assoc, h, one_mul]

theorem tie_w : ∀ g < 18, 2 ≤ g →
    WDL (g - 2) = (WDL (g - 2)).dropLast ++ [2 * g] ∧ ∀ c ∈ (WDL (g - 2)).dropLast, c / 2 < g := by
  decide +kernel

@[expose] noncomputable def cEl (g : ℕ) : J Ds :=
  if g = 0 then a Ds else if g = 1 then b Ds else
    ((WDL (g - 2)).dropLast.map fun c => if _h : c / 2 < g then
      (if c % 2 = 1 then cEl (c / 2) else (cEl (c / 2))⁻¹) else 1).prod
termination_by g

theorem cEl_eq (g : ℕ) : cEl g = if g = 0 then a Ds else if g = 1 then b Ds else
    ((WDL (g - 2)).dropLast.map fun c => if c / 2 < g then
      (if c % 2 = 1 then cEl (c / 2) else (cEl (c / 2))⁻¹) else 1).prod := by
  rw [cEl]
  simp only [dite_eq_ite]

noncomputable abbrev matHom : J Ds →* Matrix (Fin (Ds).d) (Fin (Ds).d) (ZMod 5) :=
  (Units.coeHom _).comp (J Ds).subtype

theorem mat_eq (x : J Ds) : mat Ds x = matHom x := rfl

theorem mat_prod (l : List (J Ds)) : mat Ds l.prod = (l.map (mat Ds)).prod := by
  rw [mat_eq, map_list_prod]
  rfl

theorem mat_inv_of {x : J Ds} {g : ℕ} (hg : g < 18) (hx : mat Ds x = Mr g) :
    mat Ds x⁻¹ = Mi g := by
  have h1 : mat Ds x⁻¹ * mat Ds x = 1 := by
    rw [mat_eq, mat_eq, ← map_mul, inv_mul_cancel, map_one]
  calc mat Ds x⁻¹ = mat Ds x⁻¹ * (Mr g * Mi g) := by rw [pair g hg, mul_one]
    _ = Mi g := by rw [← mul_assoc, ← hx, h1, one_mul]

theorem mA_eq : mA Ds = Mr 0 :=
  CertificateChecks.KernelHN.o_mA.trans (congrArg OMs (Nat.eq_of_beq_eq_true ra).symm)

theorem mB_eq : mB Ds = Mr 1 :=
  CertificateChecks.KernelHN.o_mB.trans (congrArg OMs (Nat.eq_of_beq_eq_true rb).symm)

theorem mat_a : mat Ds (a Ds) = Mr 0 := by
  have hd : (mA Ds).det ≠ 0 := CertificateChecks.KernelHN.det_mA
  rw [mat_a' hd, mA_eq]

theorem mat_b : mat Ds (b Ds) = Mr 1 := by
  have hd : (mB Ds).det ≠ 0 := CertificateChecks.KernelHN.det_mB
  rw [mat_b' hd, mB_eq]

theorem mat_cEl : ∀ g < 18, mat Ds (cEl g) = Mr g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg
    rcases Nat.lt_or_ge g 2 with h2 | h2
    · interval_cases g
      · rw [cEl_eq, if_pos rfl, mat_a]
      · rw [cEl_eq, if_neg (by norm_num), if_pos rfl, mat_b]
    · obtain ⟨hw, hb⟩ := tie_w g hg h2
      have hroot := word_root (k := g - 2) (by omega) hg hw
      rw [cEl_eq, if_neg (by omega), if_neg (by omega), ← hroot, mat_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun c hc => ?_
      have hcg := hb c hc
      simp only [Function.comp_apply, if_pos hcg]
      rw [lm_eq]
      by_cases hp : c % 2 = 1
      · rw [if_pos hp, if_pos hp]
        exact ih _ hcg (by omega)
      · rw [if_neg hp, if_neg hp]
        exact mat_inv_of (by omega) (ih _ hcg (by omega))

end CertificateChecks.KernelHNChain

end
