module

public import Certificates.Kernel.LyModel.CdEq

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.McLMultiplier

theorem ly6110_iGX : cdEq (Ly0.wordGg ++ Ly0.wordX) (invW Ly0.wordX ++ Ly0.wordGg) = true := by
  decide +kernel

theorem ly6110_iGY : cdEq (Ly0.wordGg ++ Ly0.wordY) (invW Ly0.wordY ++ Ly0.wordGg) = true := by
  decide +kernel

theorem ly6110_iGW : cdEq (Ly0.wordGg ++ Ly0.wordW) (invW Ly0.wordW ++ Ly0.wordGg) = true := by
  decide +kernel

theorem ly6110_iU : ∀ j < 4, cdEq (Ly0.uWords.getD j [] ++ Ly0.wordY)
    (invW Ly0.wordY ++ Ly0.uWords.getD j []) = true := by
  decide +kernel

end CertificateChecks.KernelLyModel

end
