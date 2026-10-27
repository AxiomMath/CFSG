module

public import Certificates.Kernel.LyModel.CdEq

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.McLMultiplier

theorem ly6110_cYX : cdEq (Ly0.wordY ++ Ly0.wordX) (Ly0.wordX ++ Ly0.wordY) = true := by
  decide +kernel

theorem ly6110_cY3 : cdEq (Ly0.wordY ++ (Ly0.wordY ++ Ly0.wordY)) [] = true := by decide +kernel

theorem ly6110_cY1 : notB (cdEq Ly0.wordY []) = true := by decide +kernel

theorem ly6110_cYYR : notB (cdEq (Ly0.wordY ++ Ly0.wordY) (invW Ly0.wordX)) = true := by
  decide +kernel

theorem ly6110_cYR : notB (cdEq Ly0.wordY (invW Ly0.wordX)) = true := by decide +kernel

theorem ly6110_cF5 :
    cdEq (Ly0.wordF ++ (Ly0.wordF ++ (Ly0.wordF ++ (Ly0.wordF ++ Ly0.wordF)))) [] = true := by
  decide +kernel

theorem ly6110_cF1 : notB (cdEq Ly0.wordF []) = true := by decide +kernel

theorem ly6110_cFY : cdEq (Ly0.wordF ++ Ly0.wordY) (Ly0.wordY ++ Ly0.wordF) = true := by
  decide +kernel

theorem ly6110_cNY : cdEq (Ly0.wordN ++ Ly0.wordY) (Ly0.wordY ++ Ly0.wordN) = true := by
  decide +kernel

theorem ly6110_cNX : cdEq (Ly0.wordN ++ Ly0.wordX) (invW Ly0.wordX ++ Ly0.wordN) = true := by
  decide +kernel

end CertificateChecks.KernelLyModel

end
