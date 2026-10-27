module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFus
public import CFSG.RankThree.PartOne.CTP.FusionJ2Inputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.J2 5 14
  CFSG.Blueprint.NativeSporadic.J2Seed1 CFSG.Blueprint.NativeSporadic.J2Seed2

public section

namespace CertificateChecks.KernelFusLay.J2

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

theorem fus14955_K : fusL lay A B j2FusN j2FusProg j2Fus = true := by decide +kernel

theorem fus14955_neg : (!fusL lay B A j2FusN j2FusProg j2Fus) = true := by decide +kernel

end CertificateChecks.KernelFusLay.J2

end
