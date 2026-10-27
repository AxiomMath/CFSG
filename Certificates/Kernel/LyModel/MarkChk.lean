module

public import Certificates.Kernel.LyModel.CdEq

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.Sporadic.Recognition.LyonsSims

theorem ly6110_mT2 : cdEq (Ly0.wordT0 ++ Ly0.wordT0) [] = true := by decide +kernel

theorem ly6110_mT1 : notB (cdEq Ly0.wordT0 []) = true := by decide +kernel

theorem ly6110_mTX : cdEq (Ly0.wordT0 ++ Ly0.wordX) (Ly0.wordX ++ Ly0.wordT0) = true := by
  decide +kernel

theorem ly6110_mTY : cdEq (Ly0.wordT0 ++ Ly0.wordY) (Ly0.wordY ++ Ly0.wordT0) = true := by
  decide +kernel

theorem ly6110_mTW : cdEq (Ly0.wordT0 ++ Ly0.wordW) (Ly0.wordW ++ Ly0.wordT0) = true := by
  decide +kernel

end CertificateChecks.KernelLyModel

end
