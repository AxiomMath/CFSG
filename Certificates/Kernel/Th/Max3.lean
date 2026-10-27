module

public import CFSG.Certificates.Kernel.Th.Gen.Max3
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.M3_R
public import CFSG.Certificates.Kernel.Th.Checks2.M3_92
public import CFSG.Certificates.Kernel.Th.Checks2.M3_91
public import CFSG.Certificates.Kernel.Th.Checks2.M3_90
public import CFSG.Certificates.Kernel.Th.Checks2.M3_89
public import CFSG.Certificates.Kernel.Th.Checks2.M3_88
public import CFSG.Certificates.Kernel.Th.Checks2.M3_14
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble max3 Max3Data max3Chk

theorem max3_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList max3Data.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem max3_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList max3Data.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

end CertificateChecks.KernelTh

end
