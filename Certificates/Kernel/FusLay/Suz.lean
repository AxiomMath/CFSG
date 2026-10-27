module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusSuzInputs
public import CFSG.RankThree.PartOne.CTP.FusionSuzInputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.Suz 3 64
  CFSG.Blueprint.NativeSporadic.SuzSeed1 CFSG.Blueprint.NativeSporadic.SuzSeed2

public section

namespace CertificateChecks.KernelFusLay.Suz

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

theorem fus9472_K : fusL lay A B betaSuzP3N betaSuzP3Prog betaSuzP3 = true := by decide +kernel

theorem fus14957_K : fusL lay A B suzFusN suzFusProg suzFus = true := by decide +kernel

theorem fus9472_neg : (!fusL lay B A betaSuzP3N betaSuzP3Prog betaSuzP3) = true := by
  decide +kernel

theorem fus14957_neg : (!fusL lay B A suzFusN suzFusProg suzFus) = true := by decide +kernel

end CertificateChecks.KernelFusLay.Suz

end
