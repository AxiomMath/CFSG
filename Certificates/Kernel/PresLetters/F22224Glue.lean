module

public import Certificates.Data.GrSLitL34FactsSpMultJ3UC
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.Kernel.TabMatGrpSound
import Certificates.Kernel.PresLetters.F22224YA
import Certificates.Kernel.PresLetters.F22224H
import Certificates.Kernel.PresLetters.F22224J
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Three
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator
import all Certificates.Data.GrSLitL34FactsSpMultJ3Check
import all Certificates.Data.GrSLitL34FactsSpMultJ3UC
public import CFSG.Sporadic.J3.Group
public import Certificates.Data.CFSGNative.J3.Data

public section

namespace CertificateChecks.KernelPresLetters.F22224Glue

open CFSG.KC.TabMatGrp CFSG.Sporadic.J3 CFSG.Certificates CertificateChecks.KernelLC.J3Ops
  CFSG.Sporadic.Bridge.TwoGen CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.ComponentClassification.GSThmB.SpMult

private theorem uc_rels : ucRels.map encW = CFSG.KBRoute.F22224Y12.rels := by decide +kernel

private theorem uc_subs : [encW ucU, encW ucC] = CFSG.KBRoute.F22224Y12.T1.words := by
  decide +kernel

private theorem gamma_rels : gammaRels.map encW = CFSG.KBRoute.F22224H.rels := by decide +kernel

theorem uc_index :
    (Subgroup.closure {ucUe, ucCe}).FiniteIndex ∧ (Subgroup.closure {ucUe, ucCe}).index ≤ 6156 := by
  have h := CFSG.KBFact.F22224Y12
  rw [← uc_rels, ← uc_subs] at h
  unfold KB.TableFact at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, htop⟩ := h
  have e : KB.wordSub (pgGen ucRels) [encW ucU, encW ucC] = Subgroup.closure {ucUe, ucCe} := by
    rw [KB.wordSub]
    congr 1
    ext g
    simp [sword_pgGen, ucUe, ucCe, eq_comm]
  rw [← e]
  exact index_le_of_tableOk ucRels rfl h (by norm_num) htop

theorem gamma_card : Finite (PG 2 gammaRels) ∧ Nat.card (PG 2 gammaRels) ≤ 8160 := by
  have h := CFSG.KBFact.F22224H
  rw [← gamma_rels] at h
  exact TableFact.card gammaRels (by norm_num) h

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
  exact seedsK_det F22224J.chk

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

private theorem signedProd_shift {G : Type*} [Group G] (x : Fin 4 → G) (s : ℕ)
    (w : List (Fin 2 × Bool)) :
    signedProd x (F22224J.shiftW s w) = signedProd (fun i : Fin 2 => x (Fin.ofNat 4 (i.val + s))) w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [F22224J.shiftW, List.map_cons, signedProd_cons, signedProd_cons, ← F22224J.shiftW, ih]

private noncomputable abbrev σ : Fin 2 → J Native.j3Data := ![a Native.j3Data, b Native.j3Data]

private theorem pair_one {w : List (Fin 4 × Bool)} (hw : w ∈ F22224J.words) :
    signedProd (fun i : Fin 4 => segVal σ F22224J.segs i.val) w = 1 := by
  have hm : (w, ([] : List (Fin 2 × Bool))) ∈ F22224J.relPs F22224J.words :=
    List.mem_map.2 ⟨w, hw, rfl⟩
  have h := grpK_sound Subtype.val_injective hA hB F22224J.segs (by decide)
    (F22224J.relPs F22224J.words) F22224J.chk _ hm
  rwa [signedProd_nil, mul_one] at h

private theorem img2_eq : (fun i : Fin 2 => img2 (a Native.j3Data) (b Native.j3Data) i.val) = σ := by
  funext i
  fin_cases i <;> rfl

private theorem seg_ab : (fun i : Fin 2 => segVal σ F22224J.segs (Fin.ofNat 4 (i.val + 0)).val) =
    σ := by
  funext i
  fin_cases i <;> simp [segVal, F22224J.segs, signedProd]

private theorem seg_uc : (fun i : Fin 2 => segVal σ F22224J.segs (Fin.ofNat 4 (i.val + 2)).val) =
    ![signedProd σ ucU, signedProd σ ucC] := by
  funext i
  fin_cases i <;> rfl

theorem ab_words {w : List (Fin 2 × Bool)} (hw : w ∈ ucABWords) :
    FreeGroup.lift (fun i : Fin 2 => img2 (a Native.j3Data) (b Native.j3Data) i.val)
      (FreeGroup.mk w) = 1 := by
  have h := pair_one (w := F22224J.shiftW 0 w)
    (List.mem_append_left _ (List.mem_map.2 ⟨w, hw, rfl⟩))
  rw [signedProd_shift, seg_ab] at h
  rw [lift_mk_eq_signedProd, img2_eq, h]

theorem uc_words {w : List (Fin 2 × Bool)} (hw : w ∈ gammaJ3Words) :
    FreeGroup.lift ![FreeGroup.lift (fun i : Fin 2 => img2 (a Native.j3Data) (b Native.j3Data) i.val)
        (FreeGroup.mk ucU),
      FreeGroup.lift (fun i : Fin 2 => img2 (a Native.j3Data) (b Native.j3Data) i.val)
        (FreeGroup.mk ucC)] (FreeGroup.mk w) = 1 := by
  have h := pair_one (w := F22224J.shiftW 2 w)
    (List.mem_append_right _ (List.mem_map.2 ⟨w, hw, rfl⟩))
  rw [signedProd_shift, seg_uc] at h
  rw [lift_mk_eq_signedProd, lift_mk_eq_signedProd, lift_mk_eq_signedProd, img2_eq, h]

end CertificateChecks.KernelPresLetters.F22224Glue

end
