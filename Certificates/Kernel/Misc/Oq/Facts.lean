module

public import CFSG.Certificates.Kernel.Misc.OqBlkSound
import Certificates.Kernel.Misc.Oq.BlkL
import Certificates.Kernel.Misc.Oq.BlkU0
import Certificates.Kernel.Misc.Oq.BlkU1
import Certificates.Kernel.Misc.Oq.BlkU2

public section

namespace CertificateChecks.KernelMisc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Misc.Oq CFSG.KC.LQT.P

theorem stabL_parts : stabP false = partsL.flatten := by
  simp [stabP, partsL, stabPL, List.append_assoc]

theorem stabU_parts : stabP true = partsU.flatten := by
  simp [stabP, partsU, stabPU, List.append_assoc]

theorem blocksL : ∀ i < 9,
    blkK (b2n false) 8 (repP false) (brP false) (fstIK (invD false)) (partsL.getD i []) i = true :=
  fun i hi => by
    rw [← getLL_eq]
    exact allN_iff'.1 blkL i hi

theorem blocksU : ∀ i < 30,
    blkK (b2n true) 4 (repP true) (brP true) (fstIK (invD true)) (partsU.getD i []) i = true :=
  fun i hi => by
    rw [← getLL_eq]
    have hall : ∀ j < 3, ∀ k < 10, okUs j k = true := fun j hj k hk =>
      match j, hj with
      | 0, _ => allN_iff'.1 blkU0 k hk
      | 1, _ => allN_iff'.1 blkU1 k hk
      | 2, _ => allN_iff'.1 blkU2 k hk
      | j + 3, h => absurd h (by omega)
    have h := hall (i / 10) (by omega) (i % 10) (Nat.mod_lt _ (by decide))
    change okU (10 * (i / 10) + i % 10) = true at h
    rw [Nat.div_add_mod] at h
    exact h

theorem krPL_eq : ∀ k, k < (killReps false).length →
    unpack6 ((krP false).getD k 0) = ((killReps false).getD k ([], [])).1 := by
  decide

theorem krPU_eq : ∀ k, k < (killReps true).length →
    unpack6 ((krP true).getD k 0) = ((killReps true).getD k ([], [])).1 := by
  decide

theorem krPL_len : (krP false).length = (killReps false).length := by
  decide

theorem krPU_len : (krP true).length = (killReps true).length := by
  decide

end CertificateChecks.KernelMisc.Oq

end
