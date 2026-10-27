module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentSInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
import Certificates.Kernel.ThLet.Checks
import Certificates.Kernel.ThCent.Consumers
import CFSG.Certificates.Kernel.ThLet.Sound
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.Th.KernelContractBase
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace CertificateChecks.KernelThLet

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.KC.ThLet CFSG.KC.Th.Spec
  CFSG.KC.Th.Spec.FwdRel CFSG.KD CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp CFSG.HardMathSupport.Dickson.I271

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))


theorem th_letters17308 :
    (∀ r ∈ CFSG.GH74.QTGen4.Recog.G23.g23Words, CFSG.GH74.QTGen4.Recog.G23.evalW
        (fun i : Fin 6 => slpJ a b TabThNative.progE (TabThNative.eIdx i.val)) r = 1) ∧
      (∀ i : Fin 6,
        slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11 *
            slpJ a b TabThNative.progE (TabThNative.eIdx i.val) =
          slpJ a b TabThNative.progE (TabThNative.eIdx i.val) *
            slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11) ∧
      slpJ a b TabThNative.progE (TabThNative.eIdx 0) ≠ 1 := by
  obtain ⟨hA, hB, -, hk⟩ := KernelThCent.fwd_mats
  have hR : ∀ r, pkMat (runPk ThS.c ThS.rm ThS.ONE TabThNative.progE
      (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) r) = 𝕄 (slpJ a b TabThNative.progE r) := by
    intro r
    rw [pkMat_runPk hk _ (by decide +kernel) _ _ (pkMat_initPk hk a b hA hB), KernelThCent.slpJ_eq]
    rfl
  have h := ch17308
  rw [runK_eq] at h
  generalize runPk ThS.c ThS.rm ThS.ONE TabThNative.progE
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) = R at hR h
  unfold letOK17308 at h
  obtain ⟨hrel, h⟩ := thLet_andB.1 h
  obtain ⟨hpair, hne⟩ := thLet_andB.1 h
  have hpair := pairsOK_spec hpair
  set g : Fin 6 → J := fun i => slpJ a b TabThNative.progE (TabThNative.eIdx i.val) with hg
  have hE : ∀ i : Fin 6, pkMat (R (TabThNative.eIdx i.val)) = 𝕄 (g i) := fun i => hR _
  have hEi : ∀ i : Fin 6, pkMat (R (TabThNative.eiIdx i.val)) = 𝕄 (g i)⁻¹ := by
    intro i
    refine (mat_inv_eq ?_).symm
    rw [← hE i, ← pkMat_mulB hk, (hpair i.val i.isLt).1, pkMat_one hk]
  have hs : 𝕄 (slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11) =
      pkMat (R 11) := by
    rw [hR 11, KernelThCent.slpJ_eq, KernelThCent.slpJ_eq]
    unfold slpG
    rw [TabThNative.progE, List.foldl_append]
    exact congrArg (fun x : J => 𝕄 x)
      (foldl_opG_apply_of_lt _ 15 _ (by decide +kernel) (by decide)).symm
  refine ⟨fun r hr => ?_, fun i => ?_, ?_⟩
  · have e := pkMat_relFrom hk g (E := fun k => R (TabThNative.eIdx k))
      (Ei := fun k => R (TabThNative.eiIdx k)) hE hEi r ThS.ONE 1
      ((pkMat_one hk).trans mat_one.symm)
    rw [relsOK_spec hrel r hr, one_mul, pkMat_one hk] at e
    rw [CFSG.GH74.QTGen4.Recog.G23.evalW, FreeGroup.lift_mk]
    exact mat_injective (e.symm.trans mat_one.symm)
  · apply mat_injective
    change 𝕄 (_ * g i) = 𝕄 (g i * _)
    rw [mat_mul, mat_mul, hs, ← hE i, ← pkMat_mulB hk, ← pkMat_mulB hk, (hpair i.val i.isLt).2]
  · intro h1
    have e : pkMat (mulB ThS.c ThS.rm (R (TabThNative.eIdx 0)) ThS.ONE) = pkMat ThS.ONE := by
      rw [pkMat_mulB hk, pkMat_one hk, Matrix.mul_one]
      have h0 : g 0 = 1 := h1
      exact (hE 0).trans (by rw [h0, mat_one])
    have := pkMat_inj (inLayout_mulB hk _ _) (inLayout_one hk) e
    rw [this, Nat.beq_refl] at hne
    exact absurd hne (by decide)

end CertificateChecks.KernelThLet

end
