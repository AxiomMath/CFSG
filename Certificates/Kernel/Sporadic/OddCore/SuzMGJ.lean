module

public import Certificates.Kernel.Sporadic.OddCore.SuzMGJD
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.OddCore.SuzMGCG
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGJ 0 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGJ 1 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGJ 2 0 7
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGJ 0 0 15
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGJ 1 0 16
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGJ 2 0 1
#ks_rawchain_sl2_join CertificateChecks.KernelSpor.SuzMGJ

namespace CertificateChecks.KernelSpor.SuzMGJC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Sporadic.SuzRecog.ModelGroupsData
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF

theorem kS : allN 7 (fun j => Nat.beq (SuzMGJ.S j) (SuzMGJH.F j)) = true := by quickRfl

theorem kBase : allN 3 (fun t => Nat.beq j0rhoBase.toArray[t]! (pg 11 (mask 11) SuzMGJ.BP t)) =
    true := by quickRfl

theorem kPerm : allN 7 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzMGJ.S j)
    (SuzMGJ.SI j)) = true := by quickRfl

theorem kOrb : (List.range 3).map (fun i => rcnt (SuzMGJ.LR i)) = [120, 126, 4] := by
  decide +kernel

theorem kGen : (canonK 1782 11 (mask 11) (1782 * 11) (SuzMGJH.F 0) &&
    canonK 1782 11 (mask 11) (1782 * 11) (SuzMGJH.F 1) &&
    canonK 1782 11 (mask 11) (1782 * 11) (SuzMGJH.F 2) &&
    Nat.beq (SuzMGJH.F 0) (SuzTP 1) && Nat.beq (SuzMGJH.F 1) (SuzC1BT 9) &&
    Nat.beq (SuzMGJH.F 2) (SuzTwG 2)) = true := by quickRfl

theorem negS : Bool.not (allN 7 (fun j => Nat.beq (Nat.xor (SuzMGJ.S j) 1) (SuzMGJH.F j))) =
    true := by quickRfl

theorem binds : Binds 1782 11 SuzMGJ.S 7 3 SuzMGJ.BP j0rhoStrongArrs j0rhoBase.toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [j0rhoStrongArrs],
    SuzMGCG.strong_bind SuzMGJH.eq SuzMGJH.all kS, by simp [j0rhoBase],
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec kBase t ht)⟩

theorem pJ {j : Nat} (hj : j < 7) (hc : canonK 1782 11 (mask 11) (1782 * 11) (SuzMGJH.F j) = true) :
    P (j0rhoStrong j) (SuzMGJH.F j) :=
  ⟨SuzMGF.hexJ_eq SuzMGJH.eq SuzMGJH.all hj, hc⟩

theorem j0rho15099 : j0rhoOK = true := by
  have hg := kGen
  simp only [Bool.and_eq_true] at hg
  have hch : chainOK j0rhoStrongArrs 3 j0rhoBase j0rhoWords [120, 126, 4] = true :=
    SuzMGCG.chainOK_of (NS := 223) (CH := 8) binds (by simp [j0rhoWords])
      (fun j hj => by interval_cases j <;> rfl) (by simp only [SuzMGJD.deriv, Array.toArray_toList]) SuzMGJ.head SuzMGJ.hl
      (by norm_num) SuzMGJ.hs kPerm kOrb (by norm_num)
  unfold j0rhoOK zA
  rw [hch, eqA_P (pJ (by norm_num) hg.1.1.1.1.1) pT1,
    eqA_P (pJ (by norm_num) hg.1.1.1.1.2) SuzC1BF.pz,
    eqA_P (pJ (by norm_num) hg.1.1.1.2) pRho, Nat.eq_of_beq_eq_true hg.1.1.2,
    Nat.eq_of_beq_eq_true hg.1.2, Nat.eq_of_beq_eq_true hg.2]
  simp [j0rhoStrongArrs]

end CertificateChecks.KernelSpor.SuzMGJC

end
