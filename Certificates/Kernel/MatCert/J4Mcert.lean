module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.MatCert.J4Seeds
public import CFSG.RankThree.Asc83Table.J4Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

theorem j4_K : mcertN (opsF2K 112) JA.M JB.M CFSG.RankThree.Asc83Table.J4.j4Cert = true := by
  quickRfl

theorem j4_neg : (!mcertN (opsF2K 112) JA.M JB.M ⟨2, [], [.ord 0 3]⟩) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
