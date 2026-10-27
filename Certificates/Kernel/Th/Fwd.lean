module

public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.Ot_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_K
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Pf
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_F
public import CFSG.Certificates.Kernel.Th.Checks2.Ot_R
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble fwd FwdData fwdChkGen

theorem fwd_pins : fwdPins fwdData = true := by decide +kernel

theorem fwd_chk : fwdChk fwdData = true := andB_true fwd_ok fwd_pins

theorem fwd_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList fwdData.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem fwd_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList fwdData.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

end CertificateChecks.KernelTh

end
