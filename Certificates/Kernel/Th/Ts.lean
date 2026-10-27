
module

public import CFSG.Certificates.Kernel.Th.Gen.Ts
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Ts_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.M3_R
public import CFSG.Certificates.Kernel.Th.Checks2.Ts_R
public import CFSG.Certificates.Kernel.Th.Checks2.Ts_13
public import CFSG.Certificates.Kernel.Th.Checks2.Ts_24
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble ts TsData tsChk

theorem ts_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList tsData.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem ts_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList tsData.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

theorem ts_hThTs_Lpx : CFSG.Sporadic.ThSchreier.localPermX = (CFSG.Sporadic.ThSchreier.natsOf (String.ofList tsData.ThTs_Lpx)).toArray := by
  kernel_exact CFSG.KD.ThTs.Lpx_eq

theorem ts_hThTs_Lpy : CFSG.Sporadic.ThSchreier.localPermY = (CFSG.Sporadic.ThSchreier.natsOf (String.ofList tsData.ThTs_Lpy)).toArray := by
  kernel_exact CFSG.KD.ThTs.Lpy_eq

theorem ts_hThTs_Lrows : CFSG.Sporadic.ThSchreier.localRowsTxt = String.ofList tsData.ThTs_Lrows := by
  kernel_exact CFSG.KD.ThTs.Lrows_eq

theorem ts_hThTs_Ltla : CFSG.Sporadic.ThSchreier.localTreeLab = (CFSG.Sporadic.ThSchreier.natsOf (String.ofList tsData.ThTs_Ltla)).toArray := by
  kernel_exact CFSG.KD.ThTs.Ltla_eq

theorem ts_hThTs_Ltp : CFSG.Sporadic.ThSchreier.localTreePts = (CFSG.Sporadic.ThSchreier.natsOf (String.ofList tsData.ThTs_Ltp)).toArray := by
  kernel_exact CFSG.KD.ThTs.Ltp_eq

theorem ts_hThTs_Ltpa : CFSG.Sporadic.ThSchreier.localTreePar = (CFSG.Sporadic.ThSchreier.natsOf (String.ofList tsData.ThTs_Ltpa)).toArray := by
  kernel_exact CFSG.KD.ThTs.Ltpa_eq

end CertificateChecks.KernelTh

end
