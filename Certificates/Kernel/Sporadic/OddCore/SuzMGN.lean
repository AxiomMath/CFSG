module

public import Certificates.Kernel.Sporadic.OddCore.SuzMGND
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.OddCore.SuzMGCG
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGN 0 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGN 1 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGN 2 0 7
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGN 0 0 6
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGN 1 0 120
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGN 2 0 2
#ks_rawchain_sl2_join CertificateChecks.KernelSpor.SuzMGN

namespace CertificateChecks.KernelSpor.SuzMGNC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Sporadic.SuzRecog.ModelGroupsData
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF

local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

theorem kS : allN 9 (fun j => Nat.beq (SuzMGN.S j) (SuzMGNH.F j)) = true := by quickRfl

theorem kBase : allN 3 (fun t => Nat.beq nr0Base.toArray[t]! (pg 11 (mask 11) SuzMGN.BP t)) =
    true := by quickRfl

theorem kPerm : allN 9 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzMGN.S j)
    (SuzMGN.SI j)) = true := by quickRfl

theorem kOrb : (List.range 3).map (fun i => rcnt (SuzMGN.LR i)) = [42, 960, 12] := by
  decide +kernel

theorem kGen : (cn (SuzMGNH.F 0) && cn (SuzMGNH.F 1) && cn (SuzMGNH.F 2) && cn (SuzMGNH.F 3) &&
    cn (SuzMGNH.F 4) && Nat.beq (SuzMGNH.F 0) (SuzTP 1) && Nat.beq (SuzMGNH.F 1) (SuzC1BT 9) &&
    Nat.beq (SuzMGNH.F 2) (SuzTwG 6) && Nat.beq (SuzMGNH.F 3) (SuzTwG 2) &&
    Nat.beq (SuzMGNH.F 4) (SuzMGG 4)) = true := by quickRfl

theorem negS : Bool.not (allN 9 (fun j => Nat.beq (Nat.xor (SuzMGN.S j) 1) (SuzMGNH.F j))) =
    true := by quickRfl

theorem binds : Binds 1782 11 SuzMGN.S 9 3 SuzMGN.BP nr0StrongArrs nr0Base.toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [nr0StrongArrs],
    SuzMGCG.strong_bind SuzMGNH.eq SuzMGNH.all kS, by simp [nr0Base],
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec kBase t ht)⟩

theorem pJ {j : Nat} (hj : j < 9) (hc : cn (SuzMGNH.F j) = true) :
    P (nr0Strong j) (SuzMGNH.F j) :=
  ⟨SuzMGF.hexJ_eq SuzMGNH.eq SuzMGNH.all hj, hc⟩

theorem nr015099 : nr0OK = true := by
  have hg := kGen
  simp only [Bool.and_eq_true] at hg
  have hch : chainOK nr0StrongArrs 5 nr0Base nr0Words [42, 960, 12] = true :=
    SuzMGCG.chainOK_of (NS := 223) (CH := 8) binds (by simp [nr0Words])
      (fun j hj => by interval_cases j <;> rfl) (by simp only [SuzMGND.deriv, Array.toArray_toList]) SuzMGN.head SuzMGN.hl
      (by norm_num) SuzMGN.hs kPerm kOrb (by norm_num)
  unfold nr0OK zA tauA
  rw [hch, eqA_P (pJ (by norm_num) hg.1.1.1.1.1.1.1.1.1) pT1,
    eqA_P (pJ (by norm_num) hg.1.1.1.1.1.1.1.1.2) SuzC1BF.pz,
    eqA_P (pJ (by norm_num) hg.1.1.1.1.1.1.1.2) pW0,
    eqA_P (pJ (by norm_num) hg.1.1.1.1.1.1.2) pRho,
    eqA_P (pJ (by norm_num) hg.1.1.1.1.1.2) SuzC1BF.ptau,
    Nat.eq_of_beq_eq_true hg.1.1.1.1.2, Nat.eq_of_beq_eq_true hg.1.1.1.2,
    Nat.eq_of_beq_eq_true hg.1.1.2, Nat.eq_of_beq_eq_true hg.1.2, Nat.eq_of_beq_eq_true hg.2]
  simp [nr0StrongArrs]

end CertificateChecks.KernelSpor.SuzMGNC

end
