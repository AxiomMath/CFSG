module

public import Certificates.Kernel.Sporadic.OddCore.SuzMGKD
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.OddCore.SuzMGCG
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGK 0 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGK 1 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGK 2 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGK 3 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGK 4 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGK 5 0 7
#ks_rawchain_sl2_lvpCertificateChecks.KernelSpor.SuzMGK 6 0 7
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGK 0 0 7
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGK 1 0 3
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGK 2 0 2
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGK 3 0 2
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGK 4 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGK 5 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzMGK 6 0 1
#ks_rawchain_sl2_join CertificateChecks.KernelSpor.SuzMGK

namespace CertificateChecks.KernelSpor.SuzMGKC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Sporadic.SuzRecog.ModelGroupsData
open CertificateChecks.KernelSpor

theorem kS : allN 11 (fun j => Nat.beq (SuzMGK.S j) (SuzMGC1S.F j)) = true := by quickRfl

theorem kBase : allN 7 (fun t => Nat.beq c1Base.toArray[t]! (pg 11 (mask 11) SuzMGK.BP t)) =
    true := by quickRfl

theorem kPerm : allN 11 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzMGK.S j)
    (SuzMGK.SI j)) = true := by quickRfl

theorem kOrb : (List.range 7).map (fun i => rcnt (SuzMGK.LR i)) = [54, 20, 16, 12, 4, 2, 2] := by
  decide +kernel

theorem negS : Bool.not (allN 11 (fun j => Nat.beq (Nat.xor (SuzMGK.S j) 1) (SuzMGC1S.F j))) =
    true := by quickRfl

theorem binds : Binds 1782 11 SuzMGK.S 11 7 SuzMGK.BP c1StrongArrs c1Base.toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [c1StrongArrs],
    SuzMGCG.strong_bind SuzMGC1S.eq SuzMGC1S.all kS, by simp [c1Base],
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec kBase t ht)⟩

theorem c115099 : c1OK = true := by
  have hch : chainOK c1StrongArrs 2 c1Base c1Words [54, 20, 16, 12, 4, 2, 2] = true :=
    SuzMGCG.chainOK_of (NS := 223) (CH := 8) binds (by simp [c1Words])
      (fun j hj => by interval_cases j <;> rfl) (by simp only [SuzMGKD.deriv, Array.toArray_toList]) SuzMGK.head SuzMGK.hl
      (by norm_num) SuzMGK.hs kPerm kOrb (by norm_num)
  unfold c1OK
  rw [hch]
  simp [c1StrongArrs]

end CertificateChecks.KernelSpor.SuzMGKC

end
