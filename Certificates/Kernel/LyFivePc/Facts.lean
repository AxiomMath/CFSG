module

public import Certificates.Kernel.LyFivePc.ChecksX
public import Certificates.Kernel.LyFivePc.ChecksY
public import Certificates.Kernel.LyThree.Facts
public import Certificates.Kernel.SporSch.Ly.FiveLanes
public import CFSG.Certificates.Kernel.SlpClsPcSound
public import CFSG.RankThree.PartOne.KS.LyFiveCore
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses
public import CFSG.Sporadic.Suz.Setup

public section

namespace CertificateChecks.KernelLyFivePc

open CFSG.Sporadic.Ly CFSG.KS.Ord CFSG.KS.SlpPc CFSG.StandardType.SporadicShape
open CFSG.RankThree.Native CFSG.RankThree.PartOne.LyFive
open CertificateChecks.KernelSporSch CertificateChecks.KernelLyThree

theorem lyMat_a : lyMatHom a = ordMat 5 111 12 1332 LyBS.A := by
  rw [lyMatHom_apply, mat_a, ← toMat_matA, LyBSF.matA_eq, toMat_U]

theorem lyMat_b : lyMatHom b = ordMat 5 111 12 1332 LyBS.B := by
  rw [lyMatHom_apply, mat_b, ← toMat_matB, LyBSF.matB_eq, toMat_U]

theorem unitA : IsUnit (ordMat 5 111 12 1332 LyBS.A) := by
  rw [← lyMat_a]
  exact (Group.isUnit _).map lyMatHom

theorem unitB : IsUnit (ordMat 5 111 12 1332 LyBS.B) := by
  rw [← lyMat_b]
  exact (Group.isUnit _).map lyMatHom

theorem factsX : ∃ R, ClsPcFacts (ordMat 5 111 12 1332 LyBS.A)
    (ordMat 5 111 12 1332 LyBS.B) (ordMat 5 111 12 1332 CFSG.KD.LyFivePc.XX) CFSG.KD.LyFivePc.rxX
    CFSG.KD.LyFivePc.sgX CFSG.KD.LyFivePc.entX R :=
  clsPc_sound CFSG.KD.OrdLy.consts (by norm_num) (by norm_num) cA cB unitA unitB
    CFSG.KD.LyFivePc.chkX

theorem factsY : ∃ R, ClsPcFacts (ordMat 5 111 12 1332 LyBS.A)
    (ordMat 5 111 12 1332 LyBS.B) (ordMat 5 111 12 1332 CFSG.KD.LyFivePc.YY) CFSG.KD.LyFivePc.rxY
    CFSG.KD.LyFivePc.sgY CFSG.KD.LyFivePc.entY R :=
  clsPc_sound CFSG.KD.OrdLy.consts (by norm_num) (by norm_num) cA cB unitA unitB
    CFSG.KD.LyFivePc.chkY

theorem x_mat :
    lyMatHom lyFiveXJ = ordMat 5 111 12 1332 CFSG.KD.LyFivePc.XX := by
  rw [lyMatHom_XJ, LyFL.x_eq, toMat_U, CFSG.KD.LyFivePc.XX]

theorem y_mat :
    lyMatHom (lyFiveVJ 0 * lyFiveVJ 1) = ordMat 5 111 12 1332 CFSG.KD.LyFivePc.YY := by
  have c0 : Canon 5 111 12 (LyFL.V ((0 : Fin 4) : ℕ)) :=
    validM_canon CFSG.KD.OrdLy.consts (LyBSF.hv (LyFL.v_eq 0).2)
  have c1 : Canon 5 111 12 (LyFL.V ((1 : Fin 4) : ℕ)) :=
    validM_canon CFSG.KD.OrdLy.consts (LyBSF.hv (LyFL.v_eq 1).2)
  have hY : CFSG.KD.LyFivePc.YY = CFSG.KC.Ord.mulR 5 12 1332 111 8 CFSG.KD.OrdLy.L
      CFSG.KD.OrdLy.H CFSG.KD.OrdLy.CM CFSG.KD.OrdLy.RM (LyFL.V ((0 : Fin 4) : ℕ))
      (LyFL.V ((1 : Fin 4) : ℕ)) := rfl
  rw [map_mul, lyMatHom_VJ, lyMatHom_VJ, (LyFL.v_eq 0).1, (LyFL.v_eq 1).1, toMat_U, toMat_U, hY,
    (mulR_sound CFSG.KD.OrdLy.consts c0 c1).2]

theorem gen_x :
    ∀ z : J, IsConj lyFiveXJ z → SporKRestGenerating 5 z := by
  have : Finite J := Finite.of_injective _ lyMatHom_injective
  obtain ⟨R, hF⟩ := factsX
  rw [← lyMat_a, ← lyMat_b] at hF
  obtain ⟨x₀, e, -, g⟩ := generating_of_clsPcFacts lyMatHom lyMatHom_injective _ _ closure_ab hF
  rw [← lyMatHom_injective (e.trans x_mat.symm)]
  exact g

theorem gen_y :
    ∀ z : J, IsConj (lyFiveVJ 0 * lyFiveVJ 1) z → SporKRestGenerating 5 z := by
  have : Finite J := Finite.of_injective _ lyMatHom_injective
  obtain ⟨R, hF⟩ := factsY
  rw [← lyMat_a, ← lyMat_b] at hF
  obtain ⟨x₀, e, -, g⟩ := generating_of_clsPcFacts lyMatHom lyMatHom_injective _ _ closure_ab hF
  rw [← lyMatHom_injective (e.trans y_mat.symm)]
  exact g

theorem gen_of_isConj_pow {K : Type} [Group K] {p : ℕ} {r : K}
    (h : ∀ y : K, IsConj r y → SporKRestGenerating p y) (e : ℕ) :
    ∀ z : K, IsConj (r ^ e) z → SporKRestGenerating p z := by
  intro z hz
  obtain ⟨c, hc⟩ := isConj_iff.mp hz
  have hz' : z = (c * r * c⁻¹) ^ e := by rw [conj_pow]; exact hc.symm
  rw [hz']
  exact (h (c * r * c⁻¹) (isConj_iff.mpr ⟨c, rfl⟩)).pow e

theorem cover_J :
    SporKRestCover 5 J := by
  refine sporKRest_cover_of_classes Nat.prime_five
    (((List.range 4).map fun i => lyFiveXJ ^ (i + 1)) ++
      ((List.range 4).map fun i => (lyFiveVJ 0 * lyFiveVJ 1) ^ (i + 1))) ?_ ?_
  · intro s hs
    obtain ⟨g, r, hr, e, he1, he4, hge⟩ := lyFive_cover_J s hs
    refine ⟨r ^ e, ?_, ?_⟩
    · rw [List.mem_append]
      rcases hr with hr | hr
      · left
        rw [hr, List.mem_map]
        exact ⟨e - 1, List.mem_range.2 (by omega), by rw [Nat.sub_add_cancel he1]⟩
      · right
        rw [Set.mem_singleton_iff.1 hr, List.mem_map]
        exact ⟨e - 1, List.mem_range.2 (by omega), by rw [Nat.sub_add_cancel he1]⟩
    · rw [isConj_iff]
      exact ⟨g⁻¹, by rw [← hge]; group⟩
  · intro r hr z hz
    rw [List.mem_append, List.mem_map, List.mem_map] at hr
    rcases hr with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩
    · exact gen_of_isConj_pow gen_x (i + 1) z hz
    · exact gen_of_isConj_pow gen_y (i + 1) z hz

theorem cover_native :
    SporKRestCover 5 CFSG.Blueprint.NativeSporadic.Ly :=
  @SporKRestCover.of_mulEquiv J CFSG.Blueprint.NativeSporadic.Ly inferInstance inferInstance
    lyEquivJ.symm 5 cover_J

end CertificateChecks.KernelLyFivePc

end
