module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.W4Presentation
public import CFSG.Certificates.Kernel.TabMatGrpSound
import Certificates.Kernel.W4Model.Check
import all CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple

public section

namespace CertificateChecks.KernelW4Model

open CFSG.KC.TabMatGrp CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
  CFSG.Sporadic.J3 CFSG.Certificates CertificateChecks.KernelLC.J3Ops

private theorem MatP_A : MatP 80 SA.M = mA Native.j3Data := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound SA.bind, ← SA.eq]
  exact CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload _ _

private theorem MatP_B : MatP 80 SB.M = mB Native.j3Data := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound SB.bind, ← SB.eq]
  exact CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload _ _

private theorem dets : (mA Native.j3Data).det ≠ 0 ∧ (mB Native.j3Data).det ≠ 0 := by
  rw [← MatP_A, ← MatP_B]
  exact seedsK_det chk

private theorem hA :
    MatP 80 SA.M = matOf (J Native.j3Data).subtype (![a Native.j3Data, b Native.j3Data] 0) := by
  rw [show (![a Native.j3Data, b Native.j3Data] 0 : J Native.j3Data) = a Native.j3Data from rfl,
    matOf, Subgroup.subtype_apply, coe_a, gA, dif_pos dets.1,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_A]

private theorem hB :
    MatP 80 SB.M = matOf (J Native.j3Data).subtype (![a Native.j3Data, b Native.j3Data] 1) := by
  rw [show (![a Native.j3Data, b Native.j3Data] 1 : J Native.j3Data) = b Native.j3Data from rfl,
    matOf, Subgroup.subtype_apply, coe_b, gB, dif_pos dets.2,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_B]

private theorem uJ_eq (i : Fin 7) : uJ i = segVal ![a Native.j3Data, b Native.j3Data] segs i.val := by
  have hi : i.val < (List.range 7).length := by simp
  unfold uJ uN segVal segs
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  exact prod_pairLetter _ _ _

theorem w4_eq_one : FreeGroup.lift uJ (FreeGroup.mk (wRel 4 1)) = 1 := by
  have h := grpK_sound Subtype.val_injective hA hB segs (by rfl) [(wRel 4 1, [])] chk _
    List.mem_cons_self
  rw [signedProd_nil, mul_one] at h
  rw [lift_mk_eq_signedProd]
  rw [← h]
  congr 1
  funext i
  exact uJ_eq i

end CertificateChecks.KernelW4Model

end
