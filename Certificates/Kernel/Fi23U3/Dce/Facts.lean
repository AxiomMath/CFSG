module

public import Certificates.Kernel.Fi23U3.Dce.Walk
public import CFSG.Certificates.Kernel.TwistDce3.Sound

public section

namespace CFSG.KD.Fi23Dce3

open CFSG.KC.TwDce2 CFSG.KC.TwDce3 CFSG.Certificates.TwDce CFSG.Certificates.CosetEnumeration

@[expose] noncomputable def fiH : Subgroup fiPC :=
  Subgroup.closure {PresentedGroup.of 0, PresentedGroup.of 1, PresentedGroup.of 2}

theorem hgen_lt : ∀ c < 6, fiHGen c = 0 ∨ fiHGen c = 1 ∨ fiHGen c = 2 := by decide

theorem hxH : ∀ c < 12, fiX c ∈ fiH := by
  intro c _
  by_cases h6 : c < 6
  · have hm : (PresentedGroup.of (fiHGen c) : fiPC) ∈ fiH := by
      apply Subgroup.subset_closure
      rcases hgen_lt c h6 with e | e | e <;> rw [e] <;> simp
    rw [fiX, if_pos h6]
    split_ifs
    · exact hm
    · exact fiH.inv_mem hm
  · rw [fiX, if_neg h6]
    exact fiH.one_mem

theorem inv_eq : ∀ c < 12, ivL INVM c = if c < 6 then (if c % 2 = 0 then c + 1 else c - 1) else c := by
  decide +kernel

theorem fiHGen_congr {d e : ℕ} (h : d / 2 = e / 2) : fiHGen d = fiHGen e := by
  simp only [fiHGen, h]

theorem hinv : ∀ c < 12, ivL INVM c < 12 ∧ fiX (ivL INVM c) = (fiX c)⁻¹ := by
  intro c hc
  refine ⟨by rw [inv_eq c hc]; split_ifs <;> omega, ?_⟩
  rw [inv_eq c hc]
  by_cases h6 : c < 6
  · rw [if_pos h6]
    by_cases h : c % 2 = 0
    · rw [if_pos h]
      simp only [fiX, if_pos h6, if_pos (show c + 1 < 6 by omega), if_pos h,
        if_neg (show ¬ (c + 1) % 2 = 0 by omega), fiHGen_congr (show (c + 1) / 2 = c / 2 by omega)]
    · rw [if_neg h]
      simp only [fiX, if_pos h6, if_pos (show c - 1 < 6 by omega), if_neg h,
        if_pos (show (c - 1) % 2 = 0 by omega), inv_inv,
        fiHGen_congr (show (c - 1) / 2 = c / 2 by omega)]
  · rw [if_neg h6]
    simp [fiX, h6]

theorem nt_eq : NT = 0 := by decide +kernel

theorem psf_eq : PSF = idMap := by decide +kernel

theorem psb_eq : PSB = idMap := by decide +kernel

@[expose] noncomputable def lenBool (r : ℕ) : Bool :=
  decide (CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16) && decide (CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16)

theorem len_bool : (List.range 44010).all lenBool = true := by
  quickRfl

theorem hlenR : ∀ r < 44010, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧
    CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16 := by
  intro r hr
  have h := List.all_eq_true.1 len_bool r (List.mem_range.2 hr)
  simpa only [lenBool, Bool.and_eq_true, decide_eq_true_eq] using h

theorem facts (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => CFSG.KC.YModel.fieldAt PB (F c) p)
        (CFSG.KC.TwDce.fld BS (16 * i) 65535) = CFSG.KC.TwDce.fld BS (16 * i) 65535) →
      evalWord fiX w = 1) :
    ∃ X : ℕ → fiPC, X 0 = 1 ∧ ∀ r < 44010, dKind (RD r) < 5 ∧ dN1 (RD r) < 2735 ∧
      dN2 (RD r) < 2735 ∧
      (dKind (RD r) < 3 →
        X (dN1 (RD r)) * wVal fiX (RW r) * fiT * (X (dN2 (RD r)) * wVal fiX (RA r))⁻¹ ∈ fiH) ∧
      (3 ≤ dKind (RD r) → X (dN1 (RD r)) * (X (dN2 (RD r)) * wVal fiX (RW r))⁻¹ ∈ fiH) := by
  have hf := fold_ok
  rw [psf_eq, psb_eq] at hf
  exact CFSG.Certificates.TwDce3.dce_sound_comm hf (by norm_num) fiH fiX fiT hxH hinv
    (by rw [nt_eq]; norm_num) (fun c hc => absurd hc (by rw [nt_eq]; omega)) hWD hone hlenR

end CFSG.KD.Fi23Dce3

end
