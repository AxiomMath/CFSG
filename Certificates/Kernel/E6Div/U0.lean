module

public import Certificates.Kernel.E6WK.Data
public import Certificates.Kernel.E6Div.Data
public import Certificates.Data.Kernel.E6Div
import CFSG.Certificates.Kernel.Common.EachTrue
import all Certificates.Data.Kernel.E6Div
import all Certificates.Data.Kernel.E6WK
import all Certificates.Data.TwE6WeylKill
import all CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar

public section

open CFSG.KC.E6Div
open CFSG.KD.E6WK (vp up vk)
open CFSG.KD.E6Div (wit)

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelE6Div ch715001u
  (fun n => uCheckDiv vp (up.getD n 0) vk (wit.getD n [])) 0 14
