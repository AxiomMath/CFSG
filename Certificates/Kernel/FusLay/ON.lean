module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusONInputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.ON 3 154
  CFSG.Blueprint.NativeSporadic.ONSeed1 CFSG.Blueprint.NativeSporadic.ONSeed2

public section

namespace CertificateChecks.KernelFusLay.ON

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

theorem fus9475_K : fusL lay A B betaONP3N betaONP3Prog betaONP3 = true := by decide +kernel

theorem fus9475_neg : (!fusL lay B A betaONP3N betaONP3Prog betaONP3) = true := by
  decide +kernel

end CertificateChecks.KernelFusLay.ON

end
