module

public import Certificates.Kernel.AlphaMc.SeedsF2
public import Certificates.Kernel.J3Local.Seeds
public import Certificates.Data.Kernel.OpsF2KMcert
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusJ3Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo1Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo2Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo3Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Co1Inputs

public section

namespace CertificateChecks.KernelFusOps2

open CFSG.KC.OpsF2K CFSG.RankThree.PartOne.CTP.Fus
open CertificateChecks.KernelJ3L CertificateChecks.KernelAM

theorem betaJ3P3_K : fusK 80 JA.M JB.M betaJ3P3N betaJ3P3Prog betaJ3P3 = true := by
  decide +kernel

theorem betaCo3P3_K : fusK 22 C3A.M C3B.M betaCo3P3N betaCo3P3Prog betaCo3P3 = true := by
  decide +kernel

theorem betaCo2P3_K : fusK 22 C2A.M C2B.M betaCo2P3N betaCo2P3Prog betaCo2P3 = true := by
  decide +kernel

theorem betaCo1P3_K : fusK 24 C1A.M C1B.M betaCo1P3N betaCo1P3Prog betaCo1P3 = true := by
  decide +kernel

theorem betaCo1P5_K : fusK 24 C1A.M C1B.M betaCo1P5N betaCo1P5Prog betaCo1P5 = true := by
  decide +kernel

theorem fusD2Co1_K : fusK 24 C1A.M C1B.M fusD2Co1N fusD2Co1Prog fusD2Co1 = true := by
  decide +kernel

end CertificateChecks.KernelFusOps2
