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

meta def baseF3 : Array Nat := (CFSG.Sporadic.SuzOddCore.invFullBases.getD 3 []).toArray

meta def strongF3 : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.invFullStrongArrs 3

@[expose] def derivF3 : List (List Int) := CFSG.Sporadic.SuzOddCore.invFullDerivations.getD 3 []

end CertificateChecks.KernelSpor.SuzInv

#ks_rawchain_sl4 CertificateChecks.KernelSpor.SuzInvF3 1782 11 8 64 0
  CertificateChecks.KernelSpor.SuzInv.strongF3 CertificateChecks.KernelSpor.SuzInv.baseF3 6
  CertificateChecks.KernelSpor.SuzInv.derivF3

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem sOKF3 : allN 13 (fun j => Nat.beq (SuzInvF3.S j) (SuzInvT3.F (Nat.add 7 j))) = true := by
  quickRfl
theorem genF3 : allN 6 (fun k => Nat.beq (SuzInvT3.F (Nat.add 1 k)) (SuzInvF3.S k)) = true := by
  quickRfl
theorem baseOKF3 : allN 4 (fun t => Nat.beq (invFullBases.getD 3 []).toArray[t]!
    (pg 11 (mask 11) SuzInvF3.BP t)) = true := by quickRfl
theorem permF3 : allN 13 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzInvF3.S j)
    (SuzInvF3.SI j)) = true := by quickRfl

theorem bindsF3 : Binds 1782 11 SuzInvF3.S 13 4 SuzInvF3.BP (invFullStrongArrs 3)
    (invFullBases.getD 3 []).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [invFullStrongArrs, invFullStrongCounts],
    fun j hj => ?_, by simp [invFullBases], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKF3 t ht)⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec sOKF3 j hj)
  have hk : 1 + invFullGenCounts.getD 3 0 + j = 7 + j := by simp [invFullGenCounts]
  unfold invFullStrongArrs
  rw [getElem!_pos _ j (by simpa [invFullStrongCounts] using hj), Array.getElem_ofFn]
  change invRun 3 (1 + invFullGenCounts.getD 3 0 + j) = _
  rw [hk, run_eq3 (by omega), e]
  rfl

theorem gensF3 : (invFullGenArrs 3).size = 6 ∧
    ∀ k < 6, (invFullGenArrs 3)[k]! = unpack 1782 11 (SuzInvT3.F (Nat.add 1 k)) := by
  refine ⟨by simp [invFullGenArrs, invFullGenCounts], fun k hk => ?_⟩
  unfold invFullGenArrs
  rw [getElem!_pos _ k (by simpa [invFullGenCounts] using hk), Array.getElem_ofFn]
  change invRun 3 (1 + k) = _
  rw [run_eq3 (by omega)]
  rfl

end CertificateChecks.KernelSpor.SuzInv

end
