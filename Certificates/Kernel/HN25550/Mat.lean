module

public import CFSG.Sporadic.HN.Commutant
public import CFSG.Sporadic.HNSchreier.LevelInputs
public import Certificates.Kernel.HN25550.Regs
public import Certificates.Kernel.HN25550.Ties
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Spor.WordRegsSound
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import Certificates.Kernel.HN3166.Ord
import Certificates.Kernel.HN3166.Seed
import Certificates.Kernel.VecCert.WordProg
import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHN25550

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNMult CFSG.KD.HN25550 CFSG.Sporadic.F5 CFSG.KS.WordRegs

local notation "Ds" => CFSG.Sporadic.HNSchreier.Native.hnsData

local notation "OMs" => ordMat 5 (CFSG.Sporadic.F5.Native.F5Data.d CFSG.Sporadic.HNSchreier.Native.hnsData) 13 1729

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem decL_eq (w : List ℕ) : decL w = w.map letC := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change List.cons (letC c) (decL w) = _
    rw [ih, List.map_cons]

@[expose] noncomputable def lm (c : ℕ) : Matrix (Fin (Ds).d) (Fin (Ds).d) (ZMod 5) :=
  OMs (letM RB 46 (letC c))

@[expose] noncomputable def Mr (g : ℕ) : Matrix (Fin (Ds).d) (Fin (Ds).d) (ZMod 5) := OMs (RB (g + 1))

@[expose] noncomputable def Mi (g : ℕ) : Matrix (Fin (Ds).d) (Fin (Ds).d) (ZMod 5) := OMs (RB (47 + g))

theorem lm_eq (c : ℕ) : lm c = if c % 2 = 1 then Mr (c / 2) else Mi (c / 2) := by
  unfold lm Mr Mi
  rw [CertificateChecks.KernelWP.letC_div]
  by_cases h : c % 2 = 1
  · simp only [h, decide_true, if_true]
    rfl
  · simp only [h, decide_false, if_false]
    change OMs (RB (Nat.add (Nat.succ 46) (c / 2))) = _
    rfl

theorem sound {rels : List (List (ℕ × Bool))} (hb : relsBounded rels 46 = true)
    (hr : ∀ r < lenRels rels, relOK RB mul rels 46 CFSG.KD.OrdHN.ONE r = true ∨
      ∃ s < r, relDupOK rels s r = true) :
    (∀ g < 46, ordMat 5 133 13 1729 (RB (g + 1)) * ordMat 5 133 13 1729 (RB (46 + 1 + g)) = 1) ∧
      ∀ v ∈ rels, (v.map fun x => ordMat 5 133 13 1729 (letM RB 46 x)).prod = 1 :=
  rels_sound (p := 5) (d := 133) (w := 13) (S := 1729) (T := 9) (L := CFSG.KD.OrdHN.L)
    (H := CFSG.KD.OrdHN.H) (CM := CFSG.KD.OrdHN.CM) (RM := CFSG.KD.OrdHN.RM)
    (ONE := CFSG.KD.OrdHN.ONE) (LV := CFSG.KD.OrdHN.LV) (HV := CFSG.KD.OrdHN.HV)
    (nb := 229957) (Lg := 46) (RB := RB) CFSG.KD.OrdHN.consts rfl roots invs hb hr

theorem mul_comm_of_one {d : ℕ} {A B : Matrix (Fin d) (Fin d) (ZMod 5)} (h : A * B = 1) :
    B * A = 1 :=
  mul_eq_one_comm.mp h

theorem pair (g : ℕ) (hg : g < 46) : Mr g * Mi g = 1 := by
  have h := (sound (rels := []) rfl (fun r hr => absurd hr (Nat.not_lt_zero r))).1 g hg
  have e : 46 + 1 + g = 47 + g := by omega
  rw [e] at h
  exact h

theorem relW_one {w : List ℕ} (h : relW RB mul 46 CFSG.KD.OrdHN.ONE w = true) :
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

theorem tie_parts : RW.length = 44 ∧ REL.length = 44 ∧ rootsOK RW = true ∧
    ∀ k < 44, REL.getD k [] = RW.getD k [] ++ [2 * (k + 2)] := by
  have h := ties_ok
  unfold tiesK at h
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem word_root_of {RWl RELl : List (List ℕ)} (hRL : RELl.length = 44)
    (hrel : ∀ k < 44, RELl.getD k [] = RWl.getD k [] ++ [2 * (k + 2)])
    (hrels : RELl.all (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true) {g : ℕ} (hg : g < 46)
    (h2 : 2 ≤ g) : ((RWl.getD (g - 2) []).map lm).prod = Mr g := by
  have hk : g - 2 < RELl.length := by omega
  have hmem : RELl.getD (g - 2) [] ∈ RELl := by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have h := relW_one (List.all_eq_true.1 hrels _ hmem)
  have e : g - 2 + 2 = g := by omega
  rw [hrel (g - 2) (by omega), e, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton, lm_eq, if_neg (by omega : ¬ 2 * g % 2 = 1),
    Nat.mul_div_cancel_left g (by norm_num : 0 < 2)] at h
  have h2' : Mi g * Mr g = 1 := mul_comm_of_one (pair g hg)
  calc ((RWl.getD (g - 2) []).map lm).prod
      = ((RWl.getD (g - 2) []).map lm).prod * (Mi g * Mr g) := by rw [h2', mul_one]
    _ = Mr g := by rw [← mul_assoc, h, one_mul]

theorem word_root {g : ℕ} (hg : g < 46) (h2 : 2 ≤ g) :
    ((RW.getD (g - 2) []).map lm).prod = Mr g :=
  word_root_of tie_parts.2.1 tie_parts.2.2.2 rels hg h2

@[expose] noncomputable def rEl (g : ℕ) : J Ds :=
  if g = 0 then a Ds else if g = 1 then b Ds else
    ((RW.getD (g - 2) []).map fun c => if _h : c / 2 < g then
      (if c % 2 = 1 then rEl (c / 2) else (rEl (c / 2))⁻¹) else 1).prod
termination_by g

theorem rEl_eq (g : ℕ) : rEl g = if g = 0 then a Ds else if g = 1 then b Ds else
    ((RW.getD (g - 2) []).map fun c => if c / 2 < g then
      (if c % 2 = 1 then rEl (c / 2) else (rEl (c / 2))⁻¹) else 1).prod := by
  rw [rEl]
  simp only [dite_eq_ite]

theorem rEl_roots : RootsEq rEl RW := by
  intro g hg
  obtain ⟨-, -, hr, -⟩ := tie_parts
  rw [rEl_eq, if_neg (by omega), if_neg (by omega), wordEl]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  have hcg : c / 2 < g := by
    have := rootsOK_spec hr hc
    omega
  rw [if_pos hcg]
  rfl

noncomputable abbrev matHom : J Ds →* Matrix (Fin (Ds).d) (Fin (Ds).d) (ZMod 5) :=
  (Units.coeHom _).comp (J Ds).subtype

theorem mat_eq (x : J Ds) : mat Ds x = matHom x := rfl

theorem mat_injective : Function.Injective (mat Ds) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

theorem mat_prod (l : List (J Ds)) : mat Ds l.prod = (l.map (mat Ds)).prod := by
  rw [mat_eq, map_list_prod]
  rfl

theorem mat_one : mat Ds 1 = 1 := by
  rw [mat_eq, map_one]

theorem mat_mul (x y : J Ds) : mat Ds (x * y) = mat Ds x * mat Ds y := by
  rw [mat_eq, mat_eq, mat_eq, map_mul]

theorem mat_inv_of {x : J Ds} {g : ℕ} (hg : g < 46) (hx : mat Ds x = Mr g) :
    mat Ds x⁻¹ = Mi g := by
  have h1 : mat Ds x⁻¹ * mat Ds x = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one]
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

theorem mat_rEl : ∀ g < 46, mat Ds (rEl g) = Mr g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg
    rcases Nat.lt_or_ge g 2 with h2 | h2
    · interval_cases g
      · rw [rEl_eq, if_pos rfl, mat_a]
      · rw [rEl_eq, if_neg (by norm_num), if_pos rfl, mat_b]
    · obtain ⟨-, -, hr, -⟩ := tie_parts
      rw [rEl_eq, if_neg (by omega), if_neg (by omega), ← word_root hg h2, mat_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun c hc => ?_
      have hcg : c / 2 < g := by
        have := rootsOK_spec hr hc
        omega
      simp only [Function.comp_apply, if_pos hcg]
      rw [lm_eq]
      by_cases hp : c % 2 = 1
      · rw [if_pos hp, if_pos hp]
        exact ih _ hcg (by omega)
      · rw [if_neg hp, if_neg hp]
        exact mat_inv_of (by omega) (ih _ hcg (by omega))

theorem mat_codeEl {c : ℕ} (hc : c / 2 < 46) : mat Ds (codeEl rEl c) = lm c := by
  unfold codeEl
  rw [lm_eq]
  by_cases hp : c % 2 = 1
  · rw [if_pos hp, if_pos hp]
    exact mat_rEl _ hc
  · rw [if_neg hp, if_neg hp]
    exact mat_inv_of hc (mat_rEl _ hc)

theorem mat_wordEl {w : List ℕ} (hw : ∀ c ∈ w, c / 2 < 46) :
    mat Ds (wordEl rEl w) = (w.map lm).prod := by
  rw [wordEl, mat_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun c hc => mat_codeEl (hw c hc)

theorem wordEl_eq_one {w : List ℕ} (hw : ∀ c ∈ w, c / 2 < 46)
    (h : relW RB mul 46 CFSG.KD.OrdHN.ONE w = true) : wordEl rEl w = 1 :=
  mat_injective (by rw [mat_wordEl hw, relW_one h, mat_one])

end CertificateChecks.KernelHN25550

end
