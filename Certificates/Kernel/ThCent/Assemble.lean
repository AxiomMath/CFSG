module

public import Certificates.Kernel.Th.DceStruct
public import Certificates.Kernel.Th.Fwd

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCent

open CFSG.KC.Th.Gen CertificateChecks.KernelTh

#th_assemble thcDce DceStructData dceStructChkGen

theorem thcDce_pins : dceStructPins thcDceData = true := by decide +kernel

theorem thcDce_chk : dceStructChk thcDceData = true := andB_true thcDce_ok thcDce_pins

#th_assemble thcFwd FwdData fwdChkGen

theorem thcFwd_pins : fwdPins thcFwdData = true := by decide +kernel

theorem thcFwd_chk : fwdChk thcFwdData = true := andB_true thcFwd_ok thcFwd_pins

theorem thcFwd_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList thcFwdData.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem thcFwd_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList thcFwdData.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

theorem thcDce_LT : thcDceData.ThB_LT = CFSG.KD.ThB.LT := by kernel_exact Eq.refl CFSG.KD.ThB.LT
theorem thcDce_CB : thcDceData.ThA_CB = CFSG.KD.ThA.CB := by kernel_exact Eq.refl CFSG.KD.ThA.CB
theorem thcDce_om : thcDceData.ThB_om = CFSG.KD.ThB.om := by kernel_exact Eq.refl CFSG.KD.ThB.om
theorem thcDce_NB : thcDceData.ThB_NB = CFSG.KD.ThB.NB := by kernel_exact Eq.refl CFSG.KD.ThB.NB
theorem thcDce_NO : thcDceData.ThB_NO = CFSG.KD.ThB.NO := by kernel_exact Eq.refl CFSG.KD.ThB.NO
theorem thcDce_nT : thcDceData.ThB_nT = CFSG.KD.ThB.nT := by kernel_exact Eq.refl CFSG.KD.ThB.nT
theorem thcDce_OB : thcDceData.ThB_OB = CFSG.KD.ThB.OB := by kernel_exact Eq.refl CFSG.KD.ThB.OB
theorem thcDce_osh : thcDceData.ThB_osh = CFSG.KD.ThB.osh := by
  kernel_exact Eq.refl CFSG.KD.ThB.osh
theorem thcDce_owd : thcDceData.ThB_owd = CFSG.KD.ThB.owd := by
  kernel_exact Eq.refl CFSG.KD.ThB.owd
theorem thcDce_HB : thcDceData.ThB_HB = CFSG.KD.ThB.HB := by kernel_exact Eq.refl CFSG.KD.ThB.HB
theorem thcDce_GB : thcDceData.ThB_GB = CFSG.KD.ThB.GB := by kernel_exact Eq.refl CFSG.KD.ThB.GB
theorem thcDce_TB : thcDceData.ThB_TB = CFSG.KD.ThB.TB := by kernel_exact Eq.refl CFSG.KD.ThB.TB
theorem thcDce_E1 : thcDceData.ThB_E1 = CFSG.KD.ThB.E1 := by kernel_exact Eq.refl CFSG.KD.ThB.E1
theorem thcDce_E2 : thcDceData.ThB_E2 = CFSG.KD.ThB.E2 := by kernel_exact Eq.refl CFSG.KD.ThB.E2
theorem thcDce_E3 : thcDceData.ThB_E3 = CFSG.KD.ThB.E3 := by kernel_exact Eq.refl CFSG.KD.ThB.E3
theorem thcDce_E4 : thcDceData.ThB_E4 = CFSG.KD.ThB.E4 := by kernel_exact Eq.refl CFSG.KD.ThB.E4
theorem thcDce_E5 : thcDceData.ThB_E5 = CFSG.KD.ThB.E5 := by kernel_exact Eq.refl CFSG.KD.ThB.E5
theorem thcDce_E6 : thcDceData.ThB_E6 = CFSG.KD.ThB.E6 := by kernel_exact Eq.refl CFSG.KD.ThB.E6
theorem thcDce_E7 : thcDceData.ThB_E7 = CFSG.KD.ThB.E7 := by kernel_exact Eq.refl CFSG.KD.ThB.E7
theorem thcDce_E8 : thcDceData.ThB_E8 = CFSG.KD.ThB.E8 := by kernel_exact Eq.refl CFSG.KD.ThB.E8
theorem thcDce_E9 : thcDceData.ThB_E9 = CFSG.KD.ThB.E9 := by kernel_exact Eq.refl CFSG.KD.ThB.E9
theorem thcDce_E10 : thcDceData.ThB_E10 = CFSG.KD.ThB.E10 := by
  kernel_exact Eq.refl CFSG.KD.ThB.E10

theorem thcFwd_RBf : thcFwdData.ThS_RBf = CFSG.KD.ThS.RBf := by
  kernel_exact Eq.refl CFSG.KD.ThS.RBf
theorem thcFwd_GRf : thcFwdData.ThS_GRf = CFSG.KD.ThS.GRf := by
  kernel_exact Eq.refl CFSG.KD.ThS.GRf
theorem thcFwd_IRf : thcFwdData.ThS_IRf = CFSG.KD.ThS.IRf := by
  kernel_exact Eq.refl CFSG.KD.ThS.IRf
theorem thcFwd_Bi : thcFwdData.ThS_Bi = CFSG.KD.ThS.Bi := by kernel_exact Eq.refl CFSG.KD.ThS.Bi
theorem thcFwd_c : thcFwdData.ThS_c = CFSG.KD.ThS.c := by kernel_exact Eq.refl CFSG.KD.ThS.c
theorem thcFwd_rm : thcFwdData.ThS_rm = CFSG.KD.ThS.rm := by kernel_exact Eq.refl CFSG.KD.ThS.rm
theorem thcFwd_ONE : thcFwdData.ThS_ONE = CFSG.KD.ThS.ONE := by
  kernel_exact Eq.refl CFSG.KD.ThS.ONE

end CertificateChecks.KernelThCent

end
