module

public import CFSG.Certificates.Kernel.O8LeviSound
public import Certificates.Kernel.OmegaEight.Levi
import Certificates.Kernel.OmegaEight.Forms
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1LeviData

public section

namespace CertificateChecks.KernelO8

open CFSG.KLie.CT CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1

theorem leviCheck_eq : Model.leviCheck =
    leviCheckG 136 (genRows .minus) (Model.pArr .minus) Model.leviWord
      Model.leviRows := by
  unfold Model.leviCheck Model.leviArr
  rw [wordRows_eq]
  rfl

theorem cert3374 : Model.leviCheck = true := by
  rw [leviCheck_eq]
  refine levi_sound (n := 136) (w := 8) (m := 4) (GP := GMinus) (PP := PMinus) (L := LEVI)
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ rfl kLevi
  · intro s hs
    interval_cases s <;> rfl
  · intro s hs
    interval_cases s
    exacts [pArr0, pArr1, pArr2, pArr3]
  · intro s hs
    simp [Model.leviWord] at hs
    omega

end CertificateChecks.KernelO8

end
