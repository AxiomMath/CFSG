module

public import Certificates.Kernel.LyModel.Nets
public import Certificates.Kernel.LyModel.CdEq
public import Certificates.Data.Kernel.LyModel.Base
public import Certificates.Data.Kernel.LyModel.BaseEq

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.KC.LyBenes CFSG.KC.LyModel CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.McLMultiplier CertificateChecks.KernelLyB

theorem ly6110_sX : baseEq (yNets MS mclR0 ++ genNets NS Ly0.wordX) [] = true := by
  decide +kernel

theorem ly6110_sB : baseEq (genNets MS [2])
    (yNets MS mclSurjB ++ genNets NS (Ly0.wordX ++ Ly0.wordX)) = true := by
  decide +kernel

theorem ly6110_sD : baseEq (genNets NS [2]) (genNets MS Ly0.wordD) = true := by decide +kernel

theorem ly6110_sCAC :
    baseEq (genNets NS [1] ++ genNets MS [1] ++ genNets NS [-1]) (genNets MS Ly0.wordCAC) = true := by
  decide +kernel

theorem ly6110_sCBC :
    baseEq (genNets NS [1] ++ genNets MS [2] ++ genNets NS [-1]) (genNets MS Ly0.wordCBC) = true := by
  decide +kernel

theorem ly6110_sX3 : cdEq (Ly0.wordX ++ (Ly0.wordX ++ Ly0.wordX)) [] = true := by decide +kernel

theorem ly6110_sX1 : notB (cdEq Ly0.wordX []) = true := by decide +kernel

theorem ly6110_sCX : cdEq ([1] ++ Ly0.wordX ++ [-1]) (invW Ly0.wordX) = true := by decide +kernel

end CertificateChecks.KernelLyModel

end
