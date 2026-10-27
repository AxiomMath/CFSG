module

public import CFSG.Certificates.Kernel.Th.Gen.Seed
public import Certificates.Kernel.Th.Append
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen


noncomputable def seedData : SeedData where
  ThS_ONE := CFSG.KD.ThS.ONE
  ThS_c := CFSG.KD.ThS.c
  ThS_dg := CFSG.KD.ThS.dg
  ThS_rm := CFSG.KD.ThS.rm
  ThS_tm0 := CFSG.KD.ThS.tm0
  ThS_tm1 := CFSG.KD.ThS.tm1
  ThS_tm2 := CFSG.KD.ThS.tm2
  ThS_tm3 := CFSG.KD.ThS.tm3
  ThS_tm4 := CFSG.KD.ThS.tm4
  ThS_tm5 := CFSG.KD.ThS.tm5
  ThS_tm6 := CFSG.KD.ThS.tm6
  ThS_tm7 := CFSG.KD.ThS.tm7
  ThS_up := CFSG.KD.ThS.up
  ThSeed_LA := CFSG.KD.ThSeed.LA
  ThSeed_LB := CFSG.KD.ThSeed.LB
  ThSeed_SA := CFSG.KD.ThSeed.SA
  ThSeed_SB := CFSG.KD.ThSeed.SB
  ThSeed_SF := CFSG.KD.ThSeed.SF

theorem seed_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList seedData.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem seed_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList seedData.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

theorem seed_ok : seedChk seedData = true := by
  kernel_exact (andB_true
  (andB_true
  (andB_true
  CFSG.KD.ThS.k0
  CFSG.KD.ThSeed.dA)
  (andB_true
  CFSG.KD.ThSeed.dB
  CFSG.KD.ThSeed.pF))
  (andB_true
  (andB_true
  (eqN_of CFSG.KD.ThSeed.aa)
  (eqN_of CFSG.KD.ThSeed.bbb))
  (andB_true
  (eqN_of CFSG.KD.ThSeed.aF)
  (eqN_of CFSG.KD.ThSeed.bF))))

end CertificateChecks.KernelTh

end
