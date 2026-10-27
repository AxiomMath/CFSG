module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusMcLInputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.McL 3 21
  CFSG.Blueprint.NativeSporadic.McLSeed1 CFSG.Blueprint.NativeSporadic.McLSeed2

public section

namespace CertificateChecks.KernelFusLay.McL

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

theorem fus9471_K : fusL lay A B betaMcLP3N betaMcLP3Prog betaMcLP3 = true := by decide +kernel

theorem fus9471_neg : (!fusL lay B A betaMcLP3N betaMcLP3Prog betaMcLP3) = true := by
  decide +kernel

end CertificateChecks.KernelFusLay.McL

end
