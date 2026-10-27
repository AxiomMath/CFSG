module

public import Certificates.Kernel.Th.Fam.K
public import CFSG.Certificates.Kernel.Th.ExprSound
public import CFSG.Certificates.Kernel.Th.Gen.Max3
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.M3_R
public import CFSG.Certificates.Kernel.Th.Checks2.M3_92
public import CFSG.Certificates.Kernel.Th.Checks2.M3_91
public import CFSG.Certificates.Kernel.Th.Checks2.M3_90
public import CFSG.Certificates.Kernel.Th.Checks2.M3_89
public import CFSG.Certificates.Kernel.Th.Checks2.M3_88
public import CFSG.Certificates.Kernel.Th.Checks2.M3_14

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Gen

#th_assemble thfam Max3Data max3Chk

theorem thfam_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList thfamData.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem thfam_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList thfamData.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

theorem thfam_k : CFSG.KC.Th.Expr.kOf thfamData = thK := by
  kernel_exact (rfl : thK = thK)

theorem thCtx : CFSG.KC.Th.Expr.Ctx thK :=
  thfam_k ▸ CFSG.KC.Th.Expr.ctx_of thfamData thfam_ok thfam_hA thfam_hB

end CertificateChecks.KernelTh.Fam

end
