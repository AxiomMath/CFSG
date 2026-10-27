module

public import Certificates.Kernel.Misc.Perm.J2C3A
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data45
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data45
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelMisc.J2Fam.H1 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.h1Arr
#ks_perm CertificateChecks.KernelMisc.J2Fam.V1 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.v1Arr
#ks_perm CertificateChecks.KernelMisc.J2Fam.V2 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.v2Arr
#ks_perm CertificateChecks.KernelMisc.J2Fam.HV 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.hVArr
#ks_perm CertificateChecks.KernelMisc.J2Fam.P0 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.p0Arr
#ks_perm CertificateChecks.KernelMisc.J2Fam.OU 9 CFSG.ComponentClassification.J2Cover.outerArr
#kmisc_packarrs CertificateChecks.KernelMisc.J2Fam.GA
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.gensCaArr 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2Fam.GV
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.gensCvArr 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2Fam.WG
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.wGens 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2Fam.CC
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cConj 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2Fam.VW
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.vWits 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2Fam.TW
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.tripWit 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2Fam.NE
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.neGens 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2Fam.U4
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.u34Gens 9

public section

namespace CertificateChecks.KernelMisc.J2Fam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CertificateChecks.KernelMisc.J2M5 (okA_of)

theorem hh1 : h1Arr = unpack 315 9 H1 := arrBind_sound (by quickRfl)
theorem hv1 : v1Arr = unpack 315 9 V1 := arrBind_sound (by quickRfl)
theorem hv2 : v2Arr = unpack 315 9 V2 := arrBind_sound (by quickRfl)
theorem hhV : hVArr = unpack 315 9 HV := arrBind_sound (by quickRfl)
theorem hp0 : p0Arr = unpack 315 9 P0 := arrBind_sound (by quickRfl)
theorem hou : outerArr = unpack 315 9 OU := arrBind_sound (by quickRfl)

theorem pH1 : permB 315 9 H1 = true := by quickRfl
theorem pV1 : permB 315 9 V1 = true := by quickRfl
theorem pV2 : permB 315 9 V2 = true := by quickRfl
theorem pHV : permB 315 9 HV = true := by quickRfl
theorem pP0 : permB 315 9 P0 = true := by quickRfl
theorem pOU : permB 315 9 OU = true := by quickRfl

theorem okh1 : okA h1Arr = true := okA_of hh1 (by quickRfl) (by quickRfl) (by quickRfl)
theorem okv1 : okA v1Arr = true := okA_of hv1 (by quickRfl) (by quickRfl) (by quickRfl)
theorem okv2 : okA v2Arr = true := okA_of hv2 (by quickRfl) (by quickRfl) (by quickRfl)
theorem okhV : okA hVArr = true := okA_of hhV (by quickRfl) (by quickRfl) (by quickRfl)
theorem okp0 : okA p0Arr = true := okA_of hp0 (by quickRfl) (by quickRfl) (by quickRfl)

theorem vou : validA 315 outerArr = true := by
  rw [hou]
  exact validA_unpack (r := pinvS 315 9 (mask 9) OU) (by quickRfl)

theorem ga_size : gensCaArr.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gv_size : gensCvArr.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem wg_size : wGens.size = 6 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem cc_size : cConj.size = 3 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem vw_size : vWits.size = 12 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem tw_size : tripWit.size = 3 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ne_size : neGens.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem u4_size : u34Gens.size = 4 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem hga (k : ℕ) (hk : k < 2) : gensCaArr[k]! = unpack 315 9 (GA k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hgv (k : ℕ) (hk : k < 2) : gensCvArr[k]! = unpack 315 9 (GV k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hwg (k : ℕ) (hk : k < 6) : wGens[k]! = unpack 315 9 (WG k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hcc (k : ℕ) (hk : k < 3) : cConj[k]! = unpack 315 9 (CC k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hvw (k : ℕ) (hk : k < 12) : vWits[k]! = unpack 315 9 (VW k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem htw (k : ℕ) (hk : k < 3) : tripWit[k]! = unpack 315 9 (TW k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hne (k : ℕ) (hk : k < 2) : neGens[k]! = unpack 315 9 (NE k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hu4 (k : ℕ) (hk : k < 4) : u34Gens[k]! = unpack 315 9 (U4 k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem pGA (k : ℕ) (hk : k < 2) : permB 315 9 (GA k) = true := by interval_cases k <;> quickRfl
theorem pGV (k : ℕ) (hk : k < 2) : permB 315 9 (GV k) = true := by interval_cases k <;> quickRfl
theorem pWG (k : ℕ) (hk : k < 6) : permB 315 9 (WG k) = true := by interval_cases k <;> quickRfl
theorem pCC (k : ℕ) (hk : k < 3) : permB 315 9 (CC k) = true := by interval_cases k <;> quickRfl
theorem pVW (k : ℕ) (hk : k < 12) : permB 315 9 (VW k) = true := by interval_cases k <;> quickRfl
theorem pTW (k : ℕ) (hk : k < 3) : permB 315 9 (TW k) = true := by interval_cases k <;> quickRfl
theorem pNE (k : ℕ) (hk : k < 2) : permB 315 9 (NE k) = true := by interval_cases k <;> quickRfl
theorem pU4 (k : ℕ) (hk : k < 4) : permB 315 9 (U4 k) = true := by interval_cases k <;> quickRfl

theorem okga (k : ℕ) (hk : k < 2) : okA gensCaArr[k]! = true := by
  interval_cases k <;> exact okA_of (hga _ (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)
theorem okgv (k : ℕ) (hk : k < 2) : okA gensCvArr[k]! = true := by
  interval_cases k <;> exact okA_of (hgv _ (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)
theorem okwg (k : ℕ) (hk : k < 6) : okA wGens[k]! = true := by
  interval_cases k <;> exact okA_of (hwg _ (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)
theorem okcc (k : ℕ) (hk : k < 3) : okA cConj[k]! = true := by
  interval_cases k <;> exact okA_of (hcc _ (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)
theorem okvw (k : ℕ) (hk : k < 12) : okA vWits[k]! = true := by
  interval_cases k <;> exact okA_of (hvw _ (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)
theorem oktw (k : ℕ) (hk : k < 3) : okA tripWit[k]! = true := by
  interval_cases k <;> exact okA_of (htw _ (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)
theorem okne (k : ℕ) (hk : k < 2) : okA neGens[k]! = true := by
  interval_cases k <;> exact okA_of (hne _ (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)
theorem oku4 (k : ℕ) (hk : k < 4) : okA u34Gens[k]! = true := by
  interval_cases k <;> exact okA_of (hu4 _ (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)

end CertificateChecks.KernelMisc.J2Fam

end
