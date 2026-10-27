module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.SectionRankHS.RuSeeds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalGenURuData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem ru7genu_K : mcertN (opsF2K 28) KernelSRHS.RA.M KernelSRHS.RB.M
    ⟨2, [], ru_7_genu.facts⟩ = true := by
  quickRfl

theorem ru7genu_wf : ru_7_genu.wf = true := by decide +kernel

end CertificateChecks.KernelMC

end
