module

public import Certificates.Kernel.E6WK.Data
public import Certificates.Data.Kernel.TwE6Det.Defs
import CFSG.Certificates.Kernel.Common.EachTrue
import all Certificates.Data.Kernel.E6WK
import all Certificates.Data.TwE6WeylKill

public section

open CFSG.KC.TwE6Det CFSG.KD.E6WK

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelTwE6Det ch1609001 (fun i => chkAt vp up vk i) 135 270
