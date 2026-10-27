module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple
public import CFSG.Certificates.Kernel.TabMatGrpSound
import Certificates.Kernel.J3ModelGen.Check
import all CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple

public section

namespace CertificateChecks.KernelJ3ModelGen

open CFSG.KC.TabMatGrp CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
  CFSG.Sporadic.J3 CFSG.Certificates CertificateChecks.KernelLC.J3Ops CertificateChecks.KernelW4Model
  CFSG.Sporadic.Th CertificateChecks.KernelJ3Fusion

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

private noncomputable abbrev sig : Fin 2 → J3Model := ![a Native.j3Data, b Native.j3Data]

private theorem hA : MatP 80 SA.M = matOf (J Native.j3Data).subtype (sig 0) := by
  rw [show (sig 0 : J Native.j3Data) = a Native.j3Data from rfl,
    matOf, Subgroup.subtype_apply, coe_a, gA, dif_pos dets.1,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_A]

private theorem hB : MatP 80 SB.M = matOf (J Native.j3Data).subtype (sig 1) := by
  rw [show (sig 1 : J Native.j3Data) = b Native.j3Data from rfl,
    matOf, Subgroup.subtype_apply, coe_b, gB, dif_pos dets.2,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_B]

private theorem uJ_eq : uJ = fun i : Fin 7 => segVal sig segs i.val := by
  funext i
  have hi : i.val < (List.range 7).length := by simp
  unfold uJ uN segVal segs
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  exact prod_pairLetter _ _ _

private theorem pairs_one {q : List (Fin 7 × Bool) × List (Fin 2 × Bool)} (hq : q ∈ pairs) :
    signedProd uJ q.1 * signedProd sig q.2 = 1 := by
  rw [uJ_eq]
  exact grpK_sound Subtype.val_injective hA hB segs (by rfl) pairs chk q hq

private theorem satisfies : SatisfiesJ3Words uJ := by
  intro r hr
  have h := pairs_one (q := (r, [])) (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨r, hr, rfl⟩)))
  rw [signedProd_nil, mul_one] at h
  rw [lift_mk_eq_signedProd]
  exact h

private theorem uJ_three : uJ 3 = a Native.j3Data := by
  simp [uJ, uN, uWord, wordG, pairL]

private theorem closure_top : Subgroup.closure (Set.range uJ) = ⊤ := by
  have h := pairs_one (q := (wbWord.map zL, [(1, false)]))
    (List.mem_append.2 (Or.inr List.mem_cons_self))
  have hb : b Native.j3Data = signedProd uJ (wbWord.map zL) := by
    have e : signedProd sig [((1 : Fin 2), false)] = (b Native.j3Data)⁻¹ := by
      simp [signedProd, sig]
    rw [e, mul_inv_eq_one] at h
    exact h.symm
  have hmem : ∀ i, uJ i ∈ Subgroup.closure (Set.range uJ) := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  rw [eq_top_iff, ← closure_ab Native.j3Data, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [← uJ_three]
    exact hmem 3
  · rw [hb]
    exact signedProd_mem hmem _

theorem facts : SatisfiesJ3Words uJ ∧ Subgroup.closure (Set.range uJ) = ⊤ :=
  ⟨satisfies, closure_top⟩

end CertificateChecks.KernelJ3ModelGen

end
