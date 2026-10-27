module

public import Certificates.Kernel.TcGen.F2
public import Certificates.Kernel.TcGen.McL
public import Certificates.Kernel.TcGen.Suz
public import Certificates.Data.Kernel.OpsMcertT
public import Certificates.Data.Kernel.OpsLayT
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMSecData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMSec

open CFSG.KC.OpsK CFSG.KC.OpsMT CFSG.KC.OpsLayK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CertificateChecks.KernelTc

theorem ch40262T_mcl : mcertLT McL.lay McL.A McL.B
    ⟨mcl_7_claims.nregs, mcl_7_claims.prog, mcl_7_claims.facts⟩ = true := by
  quickRfl

theorem ch40262T_co3 : mcertT (opsF2K 22) C3A.M C3B.M
    ⟨co3_11_claims.nregs, co3_11_claims.prog, co3_11_claims.facts⟩ = true := by
  quickRfl

theorem ch40262T_suz : mcertLT Suz.lay Suz.A Suz.B
    ⟨suz_7_claims.nregs, suz_7_claims.prog, suz_7_claims.facts⟩ = true := by
  quickRfl

theorem ch40262T_wf : (mcl_7_claims.wf && co3_11_claims.wf && suz_7_claims.wf) = true := by
  decide +kernel

end CertificateChecks.KernelMSec

end
