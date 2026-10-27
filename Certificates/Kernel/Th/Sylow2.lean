module

public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_K
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Pf
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_P2
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Y2
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble sylow2 Sylow2Data sylow2ChkGen

theorem sylow2_pins : sylow2Pins sylow2Data = true := by decide +kernel

theorem sylow2_chk : sylow2Chk sylow2Data = true := andB_true sylow2_ok sylow2_pins

theorem sylow2_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList sylow2Data.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem sylow2_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList sylow2Data.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

end CertificateChecks.KernelTh

end
