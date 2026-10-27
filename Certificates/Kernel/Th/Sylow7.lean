module

public import CFSG.Certificates.Kernel.Th.Gen.Sylow7
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_K
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Pf
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_P7
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Y7
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble sylow7 Sylow7Data sylow7ChkGen

theorem sylow7_pins : sylow7Pins sylow7Data = true := by decide +kernel

theorem sylow7_chk : sylow7Chk sylow7Data = true := andB_true sylow7_ok sylow7_pins

theorem sylow7_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList sylow7Data.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem sylow7_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList sylow7Data.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

end CertificateChecks.KernelTh

end
