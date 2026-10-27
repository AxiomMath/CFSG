module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFus
public import CFSG.RankThree.PartOne.CTP.FusionHeInputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.He 7 50
  CFSG.Blueprint.NativeSporadic.HeSeed1 CFSG.Blueprint.NativeSporadic.HeSeed2

public section

namespace CertificateChecks.KernelFusLay.He

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

theorem fus14956_K : fusL lay A B heFusN heFusProg heFus = true := by decide +kernel

theorem fus14956_neg : (!fusL lay B A heFusN heFusProg heFus) = true := by decide +kernel

end CertificateChecks.KernelFusLay.He

end
