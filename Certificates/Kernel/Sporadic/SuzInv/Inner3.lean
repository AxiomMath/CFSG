module

public import Certificates.Kernel.Sporadic.RawGenSch4
public import Certificates.Kernel.Sporadic.SuzInv.Text3
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
public meta import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzInv

meta def baseI3 : Array Nat := (CFSG.Sporadic.SuzOddCore.invInnerBases.getD 3 []).toArray

meta def strongI3 : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.invInnerStrongArrs 3

@[expose] def derivI3 : List (List Int) := CFSG.Sporadic.SuzOddCore.invInnerDerivations.getD 3 []

end CertificateChecks.KernelSpor.SuzInv

#ks_rawchain_sl4 CertificateChecks.KernelSpor.SuzInvI3 1782 11 8 64 0
  CertificateChecks.KernelSpor.SuzInv.strongI3 CertificateChecks.KernelSpor.SuzInv.baseI3 5
  CertificateChecks.KernelSpor.SuzInv.derivI3

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem sOKI3 : allN 11 (fun j => Nat.beq (SuzInvI3.S j) (SuzInvT3.F (Nat.add 25 j))) = true := by
  quickRfl
theorem genI3 : allN 5 (fun k => Nat.beq (SuzInvT3.F (Nat.add 20 k)) (SuzInvI3.S k)) = true := by
  quickRfl
theorem baseOKI3 : allN 4 (fun t => Nat.beq (invInnerBases.getD 3 []).toArray[t]!
    (pg 11 (mask 11) SuzInvI3.BP t)) = true := by quickRfl
theorem permI3 : allN 11 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzInvI3.S j)
    (SuzInvI3.SI j)) = true := by quickRfl

theorem bindsI3 : Binds 1782 11 SuzInvI3.S 11 4 SuzInvI3.BP (invInnerStrongArrs 3)
    (invInnerBases.getD 3 []).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [invInnerStrongArrs, invInnerStrongCounts],
    fun j hj => ?_, by simp [invInnerBases], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKI3 t ht)⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec sOKI3 j hj)
  have hk : invInnerStart 3 + invInnerGenCounts.getD 3 0 + j = 25 + j := by
    simp [invInnerStart, invInnerGenCounts, invFullGenCounts, invFullStrongCounts]
  unfold invInnerStrongArrs
  rw [getElem!_pos _ j (by simpa [invInnerStrongCounts] using hj), Array.getElem_ofFn]
  change invRun 3 (invInnerStart 3 + invInnerGenCounts.getD 3 0 + j) = _
  rw [hk, run_eq3 (by omega), e]
  rfl

theorem gensI3 : (invInnerGenArrs 3).size = 5 ∧
    ∀ k < 5, (invInnerGenArrs 3)[k]! = unpack 1782 11 (SuzInvT3.F (Nat.add 20 k)) := by
  refine ⟨by simp [invInnerGenArrs, invInnerGenCounts], fun k hk => ?_⟩
  have hs : invInnerStart 3 + k = 20 + k := by
    simp [invInnerStart, invFullGenCounts, invFullStrongCounts]
  unfold invInnerGenArrs
  rw [getElem!_pos _ k (by simpa [invInnerGenCounts] using hk), Array.getElem_ofFn]
  change invRun 3 (invInnerStart 3 + k) = _
  rw [hs, run_eq3 (by omega)]
  rfl

end CertificateChecks.KernelSpor.SuzInv

end
