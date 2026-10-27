module

public import CFSG.Certificates.Kernel.Th.Gen.Sylow3
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_K
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Pf
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_P3
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Y3
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble sylow3 Sylow3Data sylow3ChkGen

theorem sylow3_pins : sylow3Pins sylow3Data = true := by decide +kernel

theorem sylow3_chk : sylow3Chk sylow3Data = true := andB_true sylow3_ok sylow3_pins

theorem sylow3_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList sylow3Data.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem sylow3_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList sylow3Data.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

end CertificateChecks.KernelTh

end
