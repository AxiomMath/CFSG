module

public import Certificates.Data.Kernel.OpsF2KE16
public import Certificates.Kernel.LocalComp.J3Seeds

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ3E16

open CFSG.KC.OpsF2K CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native
open CertificateChecks.KernelLC.J3Ops

theorem e16_K : e16K 80 SA.M SB.M j3E16Data = true := by decide +kernel

end CertificateChecks.KernelJ3E16

end
