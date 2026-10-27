module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverInputs
public import CFSG.Certificates.Kernel.TabMatGrpSound
import Certificates.Kernel.J3Cover.ModelCheck

public section

namespace CertificateChecks.KernelJ3Cover

open CFSG.KC.TabMatGrp CFSG.Certificates
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover
  CertificateChecks.KernelJ3Cover.Model

private theorem dets : (MatP 18 MA).det ≠ 0 ∧ (MatP 18 MB).det ≠ 0 :=
  seedsK_det chk

private noncomputable abbrev sigM : Fin 2 → GL (Fin 18) (ZMod 2) :=
  ![Matrix.GeneralLinearGroup.mkOfDetNeZero _ dets.1,
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ dets.2]

private noncomputable abbrev tauM : Fin 3 → GL (Fin 18) (ZMod 2) :=
  fun i => segVal sigM genWords i.val

private theorem hA : MatP 18 MA = matOf (MonoidHom.id (GL (Fin 18) (ZMod 2))) (sigM 0) :=
  (Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _).symm

private theorem hB : MatP 18 MB = matOf (MonoidHom.id (GL (Fin 18) (ZMod 2))) (sigM 1) :=
  (Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _).symm

private theorem model_one {w : List (Fin 3 × Bool)}
    (hw : w ∈ cover ++ [walkWord ++ walkWord ++ walkWord]) : signedProd tauM w = 1 := by
  have hm : (w, ([] : List (Fin 2 × Bool))) ∈ modelPs := by
    unfold modelPs
    exact List.mem_map.2 ⟨w, hw, rfl⟩
  have h := grpK_sound Function.injective_id hA hB genWords (by decide) modelPs chk _ hm
  rw [signedProd_nil, mul_one] at h
  exact h

private theorem walk_ne_one : signedProd tauM walkWord ≠ 1 := by
  have h := distK_sound hA hB genWords (by decide) [walkWord, []] dist 0 (by decide) 1 (by decide)
    (by decide)
  change signedProd tauM walkWord ≠ signedProd tauM [] at h
  rwa [signedProd_nil] at h

private theorem orderOf_walk : orderOf (signedProd tauM walkWord) = 3 := by
  refine orderOf_eq_prime ?_ walk_ne_one
  have h := model_one (List.mem_append_right _ (List.mem_singleton_self _))
  rw [signedProd_append, signedProd_append] at h
  rw [pow_three, ← mul_assoc]
  exact h

private theorem lift_coverS {r : FreeGroup (Fin 3)}
    (hr : r ∈ {r : FreeGroup (Fin 3) | r ∈ coverS.map FreeGroup.mk}) :
    FreeGroup.lift tauM r = 1 := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [lift_mk_eq_signedProd]
  exact model_one (List.mem_append_left _ ((List.mergeSort_perm _ _).mem_iff.1 hw))

theorem three_dvd_orderOf_walkWord :
    3 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ coverS.map FreeGroup.mk}
      (FreeGroup.mk walkWord)) := by
  have hf := orderOf_map_dvd (PresentedGroup.toGroup fun _ hr => lift_coverS hr)
    (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ coverS.map FreeGroup.mk}
      (FreeGroup.mk walkWord))
  have e : PresentedGroup.toGroup (fun _ hr => lift_coverS hr)
      (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ coverS.map FreeGroup.mk}
        (FreeGroup.mk walkWord)) = FreeGroup.lift tauM (FreeGroup.mk walkWord) := rfl
  rw [e, lift_mk_eq_signedProd, orderOf_walk] at hf
  exact hf

end CertificateChecks.KernelJ3Cover

end
