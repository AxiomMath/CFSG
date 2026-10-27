module

public import Certificates.Kernel.Sporadic.RawGenSl
public import Certificates.Kernel.Sporadic.Suz.Text2306
public meta import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz2306

meta def baseM : Array Nat := CFSG.Sporadic.SuzOddCore.smallBaseNat.toArray

@[expose] def derivs : List (List Int) := CFSG.Sporadic.SuzOddCore.smallDerivs.toList.drop 2

end CertificateChecks.KernelSpor.Suz2306

#ks_rawchain_sl CertificateChecks.KernelSpor.SuzC 1782 11 0 16 0
  CFSG.Sporadic.SuzOddCore.smallStrongArrs CertificateChecks.KernelSpor.Suz2306.baseM 2
  CertificateChecks.KernelSpor.Suz2306.derivs

namespace CertificateChecks.KernelSpor.Suz2306

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem strongOK : allN 12 (fun j => Nat.beq (SuzC.S j) (SuzSmallT.F (Nat.add j 2))) = true := by
  quickRfl

theorem baseOK : allN 6 (fun t => Nat.beq smallBaseNat.toArray[t]! (pg 11 (mask 11) SuzC.BP t)) =
    true := by
  quickRfl

theorem perm : allN 12 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzC.S j) (SuzC.SI j)) =
    true := by
  quickRfl

theorem strong_eq (j : Nat) (hj : j < 12) : smallStrongArrs[j]! = unpack 1782 11 (SuzC.S j) := by
  have e : smallStrongArrs[j]! = smallArr (j + 2) := by
    unfold smallStrongArrs
    interval_cases j <;> rfl
  rw [e, smallArr_eq (by omega), ← Nat.eq_of_beq_eq_true (allN_spec strongOK j hj)]

theorem binds : Binds 1782 11 SuzC.S 12 6 SuzC.BP smallStrongArrs smallBaseNat.toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [smallStrongArrs], strong_eq,
    by simp [smallBaseNat], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK t ht)⟩

end CertificateChecks.KernelSpor.Suz2306

end
