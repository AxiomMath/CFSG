module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi22Inputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.Fi22 3 77
  CFSG.Blueprint.NativeSporadic.Fi22Seed1 CFSG.Blueprint.NativeSporadic.Fi22Seed2

public section

namespace CertificateChecks.KernelFusLay.Fi22

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

theorem fus9478_K : fusL lay A B betaFi22P3N betaFi22P3Prog betaFi22P3 = true := by
  decide +kernel

theorem fus9478_neg : (!fusL lay B A betaFi22P3N betaFi22P3Prog betaFi22P3) = true := by
  decide +kernel

end CertificateChecks.KernelFusLay.Fi22

end
