
module

public import Certificates.Kernel.Sporadic.SuzK.Matrix
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Presentation.Suz
public import CFSG.Sporadic.Suz.SetupBase
public import Certificates.Certificate9219
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.Sporadic.Bridge CFSG.KD.SuzB CFSG.Sporadic.Suz.Native CFSG.F3.Native TauCeti

abbrev M64 : Type := Matrix (Fin 64) (Fin 64) (ZMod 3)

@[expose] noncomputable def uA : M64ˣ := ⟨ML 0, ML 0, A_sq, A_sq⟩

@[expose] noncomputable def uB : M64ˣ := ⟨ML 1, ML 2, B_B2, B2_B⟩

theorem mA_eq : SuzMats.mA = ML 0 := by
  rw [← toMat_matA]
  exact CFSG.Sporadic.Suz.toMat_matA.symm

theorem mB_eq : SuzMats.mB = ML 1 := by
  rw [← toMat_matB]
  exact CFSG.Sporadic.Suz.toMat_matB.symm

@[expose] noncomputable def seedU (i : ℕ) : M64ˣ := if i = 0 then uA else uB

@[expose] noncomputable def imgU (k : ℕ) : M64ˣ := wordProd seedU (wordAt imgWords k)

theorem val_wordProd (x : ℕ → M64ˣ) (w : List (ℕ × Bool)) :
    ((wordProd x w : M64ˣ) : M64) = SuzMats.wordM (fun i => (x i : M64)) w := by
  induction w with
  | nil => simp [wordProd, SuzMats.wordM]
  | cons l w ih =>
    simp only [wordProd, SuzMats.wordM, List.map_cons, List.prod_cons] at ih ⊢
    rw [Units.val_mul, ih]
    by_cases h : l.2 <;> simp [h, Matrix.coe_units_inv]

theorem uA_val : (uA : M64) = ML 0 := rfl
theorem uA_inv_val : ((uA⁻¹ : M64ˣ) : M64) = ML 0 := rfl
theorem uB_val : (uB : M64) = ML 1 := rfl
theorem uB_inv_val : ((uB⁻¹ : M64ˣ) : M64) = ML 2 := rfl

theorem seeds_val : (fun i => (seedU i : M64)) = SuzMats.seeds := by
  funext i
  unfold seedU SuzMats.seeds
  split_ifs
  · rw [mA_eq, uA_val]
  · rw [mB_eq, uB_val]

theorem img_val : (fun k => (imgU k : M64)) = SuzMats.img := by
  funext k
  unfold imgU SuzMats.img
  rw [val_wordProd, seeds_val]

theorem facts : SuzMats.Facts := Certificates.certificate9219

theorem rels_hold : ∀ v ∈ Sporadic.suzPresentation.relatorLetters, wordProd imgU v = 1 := by
  intro v hv
  apply Units.ext
  rw [val_wordProd, img_val, Units.val_one]
  exact facts.rels v hv

@[expose] noncomputable def phi : Sporadic.suzPresentation.Group →* M64ˣ :=
  presHom Sporadic.suzPresentation imgU rels_hold

theorem generatorCount_eq : Sporadic.suzPresentation.generatorCount = 7 := by
  simp [GroupPresentation.generatorCount]

theorem imgWords_length : imgWords.length = 7 := rfl

theorem img_mem (k : ℕ) : imgU k ∈ phi.range := by
  by_cases hk : k < 7
  · exact ⟨presGen Sporadic.suzPresentation k,
      presHom_presGen _ _ _ (by rw [generatorCount_eq]; exact hk)⟩
  · have h : wordAt imgWords k = [] := by
      unfold wordAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [imgWords_length]; omega)]
      rfl
    have e : imgU k = 1 := by
      unfold imgU
      rw [h]
      rfl
    rw [e]
    exact one_mem _

theorem uA_mem : uA ∈ phi.range := by
  have h : wordProd imgU (wordAt surjWords 0) = uA := by
    apply Units.ext
    rw [val_wordProd, img_val, facts.surjA, mA_eq, uA_val]
  rw [← h]
  exact wordProd_mem img_mem _

theorem uB_mem : uB ∈ phi.range := by
  have h : wordProd imgU (wordAt surjWords 1) = uB := by
    apply Units.ext
    rw [val_wordProd, img_val, facts.surjB, mB_eq, uB_val]
  rw [← h]
  exact wordProd_mem img_mem _

noncomputable abbrev H : Subgroup M64ˣ := Subgroup.closure {uA, uB}

private theorem presentation_eq : SporadicName.Suz.presentation = Sporadic.suzPresentation := rfl

theorem card_H : Nat.card H ≤ 448345497600 := by
  have hle : H ≤ phi.range := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact uA_mem
    · exact uB_mem
  obtain ⟨hf, hc⟩ := CFSG.Sporadic.Presentation.Suz.finite_card_le
  have hf' : Finite Sporadic.suzPresentation.Group := by
    have : Finite SporadicName.Suz.presentation.Group := hf
    rwa [presentation_eq] at this
  have hc' : Nat.card Sporadic.suzPresentation.Group ≤ 448345497600 := by
    have : Nat.card SporadicName.Suz.presentation.Group ≤ 448345497600 := hc
    rwa [presentation_eq] at this
  exact (Subgroup.card_le_of_le hle).trans
    ((Nat.card_le_card_of_surjective _ phi.rangeRestrict_surjective).trans hc')

end CertificateChecks.KernelSpor.SuzK

end
