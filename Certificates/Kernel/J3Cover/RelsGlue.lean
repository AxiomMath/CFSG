module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverInputs
public import CFSG.Certificates.Kernel.TabMatGrpSound
import Certificates.Kernel.J3Cover.Rels
public import CFSG.Sporadic.J3.Group
public import Certificates.Data.CFSGNative.J3.Data

public section

namespace CertificateChecks.KernelJ3Cover

open CFSG.KC.TabMatGrp CFSG.Sporadic.J3 CFSG.Certificates CertificateChecks.KernelLC.J3Ops
  CFSG.Sporadic.Bridge.TwoGen
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover

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
  have e : (![a Native.j3Data, b Native.j3Data] 0 : J Native.j3Data) = a Native.j3Data := rfl
  rw [e, matOf, Subgroup.subtype_apply, coe_a, gA, dif_pos dets.1,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_A]

private theorem hB :
    MatP 80 SB.M = matOf (J Native.j3Data).subtype (![a Native.j3Data, b Native.j3Data] 1) := by
  have e : (![a Native.j3Data, b Native.j3Data] 1 : J Native.j3Data) = b Native.j3Data := rfl
  rw [e, matOf, Subgroup.subtype_apply, coe_b, gB, dif_pos dets.2,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_B]

theorem lift_checkWords_eq_one {w : List (Fin 3 × Bool)} (hw : w ∈ checkWords) :
    FreeGroup.lift (fun i : Fin 3 =>
      FreeGroup.lift (fun j : Fin 2 => img2 (a Native.j3Data) (b Native.j3Data) j.val)
        (FreeGroup.mk (genWords.getD i []))) (FreeGroup.mk w) = 1 := by
  have hm : (w, ([] : List (Fin 2 × Bool))) ∈ relPs checkWords := by
    unfold relPs
    exact List.mem_map.2 ⟨w, hw, rfl⟩
  have h := grpK_sound Subtype.val_injective hA hB genWords (by decide) (relPs checkWords) chk _ hm
  rw [signedProd_nil, mul_one] at h
  rw [lift_mk_eq_signedProd, ← h]
  congr 1
  funext i
  rw [lift_mk_eq_signedProd]
  congr 1
  funext j
  fin_cases j <;> rfl

end CertificateChecks.KernelJ3Cover

end
