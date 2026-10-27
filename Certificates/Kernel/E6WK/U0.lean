module

public import Certificates.Kernel.E6WK.Data
import CFSG.Certificates.Kernel.Common.EachTrue
import all Certificates.Data.Kernel.E6WK
import all Certificates.Data.TwE6WeylKill
import all CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar

public section

open CFSG.KC.E6WK CFSG.KD.E6WK

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelE6WK ch830101u
  (fun n => uCheckWith vp rm (up.getD n 0) vk (wit.getD n [])) 0 14
