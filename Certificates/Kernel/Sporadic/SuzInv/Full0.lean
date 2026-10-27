module

public import Certificates.Kernel.Sporadic.RawGenSch3G
public import Certificates.Kernel.Sporadic.SuzInv.Text0
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
import all CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import Mathlib.Tactic.NormNum
public meta import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzInv

meta def baseF0 : Array Nat := (CFSG.Sporadic.SuzOddCore.invFullBases.getD 0 []).toArray

meta def strongF0 : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.invFullStrongArrs 0

@[expose] def derivF0 : List (List Int) := CFSG.Sporadic.SuzOddCore.invFullDerivations.getD 0 []

end CertificateChecks.KernelSpor.SuzInv

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzInvWF0
  "Certificates/Kernel/Sporadic/SuzInv/data/F0.json.gz" 450 18213716582980298408
  (W : List (List Nat))

#ks_rawchain_sl3g CertificateChecks.KernelSpor.SuzInvF0 1782 11 8 64 0
  CertificateChecks.KernelSpor.SuzInv.strongF0 CertificateChecks.KernelSpor.SuzInv.baseF0 12
  CertificateChecks.KernelSpor.SuzInv.derivF0 (4 6 10) CertificateChecks.KernelSpor.SuzInvWF0.W

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem sOKF0 : allN 19 (fun j => Nat.beq (SuzInvF0.S j) (SuzInvT0.F (Nat.add 13 j))) = true := by
  quickRfl
theorem genF0 : allN 12 (fun k => Nat.beq (SuzInvT0.F (Nat.add 1 k)) (SuzInvF0.S k)) = true := by
  quickRfl
theorem baseOKF0 : allN 3 (fun t => Nat.beq (invFullBases.getD 0 []).toArray[t]!
    (pg 11 (mask 11) SuzInvF0.BP t)) = true := by quickRfl
theorem permF0 : allN 19 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzInvF0.S j)
    (SuzInvF0.SI j)) = true := by quickRfl

theorem bindsF0 : Binds 1782 11 SuzInvF0.S 19 3 SuzInvF0.BP (invFullStrongArrs 0)
    (invFullBases.getD 0 []).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [invFullStrongArrs, invFullStrongCounts],
    fun j hj => ?_, by simp [invFullBases], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKF0 t ht)⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec sOKF0 j hj)
  have hk : 1 + invFullGenCounts.getD 0 0 + j = 13 + j := by simp [invFullGenCounts]
  unfold invFullStrongArrs
  rw [getElem!_pos _ j (by simpa [invFullStrongCounts] using hj), Array.getElem_ofFn]
  change invRun 0 (1 + invFullGenCounts.getD 0 0 + j) = _
  rw [hk, run_eq0 (by omega), e]
  rfl

theorem gensF0 : (invFullGenArrs 0).size = 12 ∧
    ∀ k < 12, (invFullGenArrs 0)[k]! = unpack 1782 11 (SuzInvT0.F (Nat.add 1 k)) := by
  refine ⟨by simp [invFullGenArrs, invFullGenCounts], fun k hk => ?_⟩
  unfold invFullGenArrs
  rw [getElem!_pos _ k (by simpa [invFullGenCounts] using hk), Array.getElem_ofFn]
  change invRun 0 (1 + k) = _
  rw [run_eq0 (by omega)]
  rfl

end CertificateChecks.KernelSpor.SuzInv

end
