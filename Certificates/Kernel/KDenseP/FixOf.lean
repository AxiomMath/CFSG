module

public import Certificates.Kernel.KDenseP.AgreeOf
public import CFSG.YGroups.Y443.Native.Align
public import CFSG.Monster.Existence.Census.Rigid

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Visible
  CFSG.Monster.Existence.Census CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum wvec

theorem wV_getD (k : ℕ) : (wV ()).D.getD k 0 = if k = 98580 then 1 else 0 := by
  unfold wV
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases hk : k < 196884
  · simp [hk]
  · have hk' : k ≠ 98580 := by omega
    simp [hk, hk']

theorem interp_wV : interp (wV ()) = wvec false 0 0 := by
  have hr : 98580 + 24 * Native.rowIdx false 0 + ((0 : Fin 24) : ℕ) = 98580 := by decide
  rw [← interp_wvec false 0 0, hr]
  apply interp_eq_of_cf
  intro k
  unfold cf
  have he : (Native.DVec.ofList [(98580, 1)]).e = 0 := rfl
  have he' : (wV ()).e = 0 := rfl
  rw [he, he', wV_getD, ofList_single_getD _ _ (by norm_num)]

theorem tStar_wvec : tStar (wvec false 0 0) = wvec false 0 0 := by
  have h1 : Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((1 : Fin 24) : ℕ)) = 191 := by decide
  have h2 := pauliQ_minus (i := 0) (j := 1) (by decide)
  rw [h1] at h2
  have hp : Model.ePauliN ⟨false, 0, 191⟩ false 0 = (false, false, 0) := by decide
  have hv := Evec_vecMul_qmatR ⟨false, 0, 191⟩ false 0
  rw [hp, ← qmatR_toSC_eq, h2] at hv
  unfold tStar rhoEquiv wvec
  rw [thetaEquiv_apply, theta_tensor, coe_rhoPair]
  simp only [ScalarKernel.mat_one, Matrix.vecMul_one, rStar_eq_rMinus, hv, sgn_boolZ]
  simp [Model.sgnI]

theorem eqv_tWord_wV :
    (Native.evalWord tWord (wV ())).eqv (wV ()) = true := by
  have hval : ∀ g ∈ tWord, g.validB = true := by decide
  refine eqv_of_interp_eq (size_evalWordC _ tWord _ size_wV) size_wV ?_
  rw [evalWord_sound tWord hval, wordLin_tWord, interp_wV, tStar_wvec]

end CertificateChecks.KernelKDenseP

end
