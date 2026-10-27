module

public import Certificates.Kernel.Sporadic.RawGenSch3G
public import Certificates.Kernel.Sporadic.SuzInv.Text1
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

meta def baseF1 : Array Nat := (CFSG.Sporadic.SuzOddCore.invFullBases.getD 1 []).toArray

meta def strongF1 : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.invFullStrongArrs 1

@[expose] def derivF1 : List (List Int) := CFSG.Sporadic.SuzOddCore.invFullDerivations.getD 1 []

end CertificateChecks.KernelSpor.SuzInv

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzInvWF1
  "Certificates/Kernel/Sporadic/SuzInv/data/F1.json.gz" 581 8225221321669896667
  (W : List (List Nat))

#ks_rawchain_sl3g CertificateChecks.KernelSpor.SuzInvF1 1782 11 8 64 0
  CertificateChecks.KernelSpor.SuzInv.strongF1 CertificateChecks.KernelSpor.SuzInv.baseF1 6
  CertificateChecks.KernelSpor.SuzInv.derivF1 (1 3) CertificateChecks.KernelSpor.SuzInvWF1.W

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem sOKF1 : allN 11 (fun j => Nat.beq (SuzInvF1.S j) (SuzInvT1.F (Nat.add 7 j))) = true := by
  quickRfl
theorem genF1 : allN 6 (fun k => Nat.beq (SuzInvT1.F (Nat.add 1 k)) (SuzInvF1.S k)) = true := by
  quickRfl
theorem baseOKF1 : allN 3 (fun t => Nat.beq (invFullBases.getD 1 []).toArray[t]!
    (pg 11 (mask 11) SuzInvF1.BP t)) = true := by quickRfl
theorem permF1 : allN 11 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzInvF1.S j)
    (SuzInvF1.SI j)) = true := by quickRfl

theorem bindsF1 : Binds 1782 11 SuzInvF1.S 11 3 SuzInvF1.BP (invFullStrongArrs 1)
    (invFullBases.getD 1 []).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [invFullStrongArrs, invFullStrongCounts],
    fun j hj => ?_, by simp [invFullBases], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKF1 t ht)⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec sOKF1 j hj)
  have hk : 1 + invFullGenCounts.getD 1 0 + j = 7 + j := by simp [invFullGenCounts]
  unfold invFullStrongArrs
  rw [getElem!_pos _ j (by simpa [invFullStrongCounts] using hj), Array.getElem_ofFn]
  change invRun 1 (1 + invFullGenCounts.getD 1 0 + j) = _
  rw [hk, run_eq1 (by omega), e]
  rfl

theorem gensF1 : (invFullGenArrs 1).size = 6 ∧
    ∀ k < 6, (invFullGenArrs 1)[k]! = unpack 1782 11 (SuzInvT1.F (Nat.add 1 k)) := by
  refine ⟨by simp [invFullGenArrs, invFullGenCounts], fun k hk => ?_⟩
  unfold invFullGenArrs
  rw [getElem!_pos _ k (by simpa [invFullGenCounts] using hk), Array.getElem_ofFn]
  change invRun 1 (1 + k) = _
  rw [run_eq1 (by omega)]
  rfl

end CertificateChecks.KernelSpor.SuzInv

end
