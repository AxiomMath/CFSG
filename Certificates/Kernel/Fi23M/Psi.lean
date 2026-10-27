
module

public import Certificates.Kernel.Fi23M.PsiBase
import all Certificates.Kernel.Fi23M.PsiBase

public import Certificates.Kernel.Fi23M.Stab
public import Certificates.Certificate9206
public import CFSG.Sporadic.Fi23.SetupBase
import Certificates.Kernel.Sporadic.Fi23Br.Rels
import Mathlib
public import Certificates.Certificate9206Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.KD.Fi23K CFSG.KC.Fi23K CFSG.KS.PC CFSG.Sporadic.Fi23 CFSG.Sporadic.Bridge.Fi23GPL.Native
  TauCeti

open CFSG.Sporadic.Fi23.Native (dWord)

section

noncomputable def X9 : ℕ → M253 :=
  Classical.choose (Certificates.certificate9206).2.2.2

theorem X9_rel : ∀ v ∈ rels (), (v.map fun l => if l.2 then X9 l.1 else (X9 l.1)⁻¹).prod = 1 :=
  (Classical.choose_spec (Certificates.certificate9206).2.2.2).2.1

theorem X9_surj0 : (((surjWords ())[0]!).map fun z =>
    if 0 < z then X9 (z - 1).toNat else (X9 (-z - 1).toNat)⁻¹).prod = mA :=
  (Classical.choose_spec (Certificates.certificate9206).2.2.2).2.2.1

theorem X9_surj1 : (((surjWords ())[1]!).map fun z =>
    if 0 < z then X9 (z - 1).toNat else (X9 (-z - 1).toNat)⁻¹).prod = mB :=
  (Classical.choose_spec (Certificates.certificate9206).2.2.2).2.2.2

theorem X9_sq {k : ℕ} (hk : k < 10) : X9 k * X9 k = 1 := by
  have h := X9_rel _ (sq_rel k hk)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true, mul_one] at h
  exact h

theorem X9_inv {k : ℕ} (hk : k < 10) : (X9 k)⁻¹ = X9 k := Matrix.inv_eq_right_inv (X9_sq hk)

noncomputable def u (k : ℕ) : M253ˣ :=
  if h : k < 10 then ⟨X9 k, X9 k, X9_sq h, X9_sq h⟩ else 1

theorem u_val {k : ℕ} (hk : k < 10) : (u k).val = X9 k := by
  unfold u
  rw [dif_pos hk]

theorem u_inv_val {k : ℕ} (hk : k < 10) : (u k)⁻¹.val = X9 k := by
  unfold u
  rw [dif_pos hk]
  rfl

theorem rels_u : ∀ w ∈ P23.relatorLetters, wordVal u w = 1 := by
  rw [relatorLetters_P23]
  intro w hw
  apply Units.ext
  have h := X9_rel w hw
  rw [Units.val_one, ← h]
  unfold wordVal
  rw [← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hl10 := rels_lt w hw l hl
  simp only [Function.comp_apply, Units.coeHom_apply]
  split_ifs
  · exact u_val hl10
  · rw [u_inv_val hl10, X9_inv hl10]

noncomputable def σ : PG →* M253ˣ := presHom P23 u rels_u

theorem σ_gen {k : ℕ} (hk : k < 10) : σ (gen k) = u k := by
  unfold gen
  rw [dif_pos (by rw [generatorCount_P23]; exact hk)]
  exact presHom_of P23 u rels_u _

theorem σ_wordP {w : List ℕ} (hw : ∀ k ∈ w, k < 10) : (σ (wordP w)).val = (w.map X9).prod := by
  unfold wordP
  rw [map_list_prod, List.map_map, ← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun k hk => by
    simp only [Function.comp_apply, Units.coeHom_apply]
    rw [σ_gen (hw k hk), u_val (hw k hk)]

theorem surj_word {i : ℕ} (hi : i < 2) :
    (((surjWords ())[i]!).map fun z => if 0 < z then X9 (z - 1).toNat else (X9 (-z - 1).toNat)⁻¹).prod =
      ((sw i).map X9).prod := by
  rw [CertificateChecks.KernelSpor.Fi23Rels.surj_eq]
  have hi' : i < CFSG.KD.BrFi23.ST.W.toArray.size := by
    rw [List.size_toArray, CertificateChecks.KernelSpor.Fi23Rels.ST_len]
    exact hi
  rw [getElem!_pos _ i hi', List.getElem_toArray]
  unfold sw
  rw [List.getD_eq_getElem _ _ (by rwa [List.size_toArray] at hi'), List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  have hzl := CertificateChecks.KernelSpor.Fi23Rels.ST_letters _ (List.getElem_mem _) z hz
  simp only [Function.comp_apply]
  split_ifs with h
  · congr 1
    omega
  · rw [X9_inv (by omega)]
    congr 1
    omega

theorem σ_wα : (σ wα).val = mA := by
  unfold wα
  rw [σ_wordP (sw_lt (by norm_num)), ← surj_word (by norm_num)]
  exact X9_surj0

theorem σ_wβ : (σ wβ).val = mB := by
  unfold wβ
  rw [σ_wordP (sw_lt (by norm_num)), ← surj_word (by norm_num)]
  exact X9_surj1

theorem σ_wZ : (σ wZ).val = mW := by
  unfold wZ
  rw [map_list_prod, List.map_map, ← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply, Units.coeHom_apply]
  unfold genMat
  split_ifs
  · exact σ_wα
  · exact σ_wβ

theorem σ_wD : (σ wD).val = mW ^ 7 := by
  unfold wD
  rw [map_pow, Units.val_pow_eq_pow_val, σ_wZ]

end

end CertificateChecks.KernelFi23M

end
