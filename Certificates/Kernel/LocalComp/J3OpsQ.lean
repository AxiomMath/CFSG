module

public import Certificates.Data.Kernel.OpsF2KQ
public import CFSG.GH74.E2.CompCertsJ3Inputs
public import Certificates.Kernel.LocalComp.J3Seeds

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.J3Ops

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CFSG.GH74.E2

theorem sec_Q : secQ 80 SA.M SB.M j3Sec = true := by decide +kernel

theorem sec_negQ : (!secQ 80 SB.M SA.M j3Sec) = true := by decide +kernel

end CertificateChecks.KernelLC.J3Ops

end
