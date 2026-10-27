module

public import Certificates.Kernel.J3Local.Seeds
public import Certificates.Kernel.TcGen.F2
public import Certificates.Data.Kernel.OpsMcertN
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMGen

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CertificateChecks.KernelTc

theorem ch40261_j3 : mcertN (opsF2K 80) KernelJ3L.JA.M KernelJ3L.JB.M
    ⟨2, [], j3_5_claims.facts⟩ = true := by
  quickRfl

theorem ch40261_co3 : mcertN (opsF2K 22) C3A.M C3B.M ⟨2, [], co3_7_claims.facts⟩ = true := by
  quickRfl

theorem ch40261_co2 : mcertN (opsF2K 22) C2A.M C2B.M ⟨2, [], co2_7_claims.facts⟩ = true := by
  quickRfl

theorem ch40261_wf : (j3_5_claims.wf && co3_7_claims.wf && co2_7_claims.wf) = true := by
  decide +kernel

end CertificateChecks.KernelMGen

end
