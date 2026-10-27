module

public import Certificates.Kernel.Sporadic.OddCore.SuzMGSD
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.Sporadic.OddCore.SuzMGCG
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGS 0 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGS 1 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGS 2 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGS 3 0 7
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGS 1 0 45
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGS 2 0 7
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGS 3 0 1
#ks_rawchain_sl2_osub CertificateChecks.KernelSpor.SuzMGS
#ks_rawchain_sl2_scho CertificateChecks.KernelSpor.SuzMGS 0 21
#ks_rawchain_sl2_joino CertificateChecks.KernelSpor.SuzMGS

namespace CertificateChecks.KernelSpor.SuzMGSC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Sporadic.SuzRecog.ModelGroupsData
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF

local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

theorem kS : allN 9 (fun j => Nat.beq (SuzMGS.S j) (SuzMGSH.F j)) = true := by quickRfl

theorem kBase : allN 4 (fun t => Nat.beq csplitBase.toArray[t]! (pg 11 (mask 11) SuzMGS.BP t)) =
    true := by quickRfl

theorem kPerm : allN 9 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzMGS.S j)
    (SuzMGS.SI j)) = true := by quickRfl

theorem kOrb : (List.range 4).map (fun i => rcnt (SuzMGS.LR i)) = [162, 360, 56, 3] := by
  decide +kernel

theorem kGen : (cn (SuzMGSH.F 0) && cn (SuzMGSH.F 1) && cn (SuzMGSH.F 2) && cn (SuzMGSH.F 3) &&
    Nat.beq (SuzMGSH.F 0) (SuzTP 1) && Nat.beq (SuzMGSH.F 1) (SuzC1BT 9) &&
    Nat.beq (SuzMGSH.F 2) (SuzTwG 2) && Nat.beq (SuzMGSH.F 3) (SuzMGG 0)) = true := by quickRfl

theorem negS : Bool.not (allN 9 (fun j => Nat.beq (Nat.xor (SuzMGS.S j) 1) (SuzMGSH.F j))) =
    true := by quickRfl

theorem binds : Binds 1782 11 SuzMGS.S 9 4 SuzMGS.BP csplitStrongArrs csplitBase.toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [csplitStrongArrs],
    SuzMGCG.strong_bind SuzMGSH.eq SuzMGSH.all kS, by simp [csplitBase],
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec kBase t ht)⟩

theorem pJ {j : Nat} (hj : j < 9) (hc : cn (SuzMGSH.F j) = true) :
    P (csplitStrong j) (SuzMGSH.F j) :=
  ⟨SuzMGF.hexJ_eq SuzMGSH.eq SuzMGSH.all hj, hc⟩

theorem csplit15099 : csplitOK = true := by
  have hg := kGen
  simp only [Bool.and_eq_true] at hg
  have hch : chainOK csplitStrongArrs 4 csplitBase csplitWords [162, 360, 56, 3] = true :=
    SuzMGCG.chainOK_of (NS := 223) (CH := 8) binds (by simp [csplitWords])
      (fun j hj => by interval_cases j <;> rfl) (by simp only [SuzMGSD.deriv, Array.toArray_toList]) SuzMGS.head SuzMGS.hl
      (by norm_num) SuzMGS.hs kPerm kOrb (by norm_num)
  unfold csplitOK zA
  rw [hch, eqA_P (pJ (by norm_num) hg.1.1.1.1.1.1.1) pT1,
    eqA_P (pJ (by norm_num) hg.1.1.1.1.1.1.2) SuzC1BF.pz,
    eqA_P (pJ (by norm_num) hg.1.1.1.1.1.2) pRho,
    eqA_P (pJ (by norm_num) hg.1.1.1.1.2) SuzMGF.pAa,
    Nat.eq_of_beq_eq_true hg.1.1.1.2, Nat.eq_of_beq_eq_true hg.1.1.2,
    Nat.eq_of_beq_eq_true hg.1.2, Nat.eq_of_beq_eq_true hg.2]
  simp [csplitStrongArrs]

end CertificateChecks.KernelSpor.SuzMGSC

end
