module

public import CFSG.Certificates.Kernel.Th.Gen.Sylow5
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_K
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Pf
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_P5
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Y5
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble sylow5 Sylow5Data sylow5ChkGen

theorem sylow5_pins : sylow5Pins sylow5Data = true := by decide +kernel

theorem sylow5_chk : sylow5Chk sylow5Data = true := andB_true sylow5_ok sylow5_pins

theorem sylow5_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList sylow5Data.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem sylow5_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList sylow5Data.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

end CertificateChecks.KernelTh

end
