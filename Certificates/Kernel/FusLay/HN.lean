module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusHNInputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.HN 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

public section

namespace CertificateChecks.KernelFusLay.HN

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

theorem fus9480_K : fusL lay A B betaHNP3N betaHNP3Prog betaHNP3 = true := by decide +kernel

theorem fus9481_K : fusL lay A B betaHNP5N betaHNP5Prog betaHNP5 = true := by decide +kernel

theorem fus9480_neg : (!fusL lay B A betaHNP3N betaHNP3Prog betaHNP3) = true := by
  decide +kernel

theorem fus9481_neg : (!fusL lay B A betaHNP5N betaHNP5Prog betaHNP5) = true := by
  decide +kernel

end CertificateChecks.KernelFusLay.HN

end
