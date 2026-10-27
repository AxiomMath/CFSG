module

public import Certificates.Kernel.Sporadic.RawGenSch3G
public import Certificates.Kernel.Sporadic.SuzInv.Text2
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

meta def baseF2 : Array Nat := (CFSG.Sporadic.SuzOddCore.invFullBases.getD 2 []).toArray

meta def strongF2 : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.invFullStrongArrs 2

@[expose] def derivF2 : List (List Int) := CFSG.Sporadic.SuzOddCore.invFullDerivations.getD 2 []

end CertificateChecks.KernelSpor.SuzInv

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzInvWF2
  "Certificates/Kernel/Sporadic/SuzInv/data/F2.json.gz" 219 11253019283225597654
  (W : List (List Nat))

#ks_rawchain_sl3g CertificateChecks.KernelSpor.SuzInvF2 1782 11 8 64 0
  CertificateChecks.KernelSpor.SuzInv.strongF2 CertificateChecks.KernelSpor.SuzInv.baseF2 3
  CertificateChecks.KernelSpor.SuzInv.derivF2 (1 7) CertificateChecks.KernelSpor.SuzInvWF2.W

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem sOKF2 : allN 8 (fun j => Nat.beq (SuzInvF2.S j) (SuzInvT2.F (Nat.add 4 j))) = true := by
  quickRfl
theorem genF2 : allN 3 (fun k => Nat.beq (SuzInvT2.F (Nat.add 1 k)) (SuzInvF2.S k)) = true := by
  quickRfl
theorem baseOKF2 : allN 3 (fun t => Nat.beq (invFullBases.getD 2 []).toArray[t]!
    (pg 11 (mask 11) SuzInvF2.BP t)) = true := by quickRfl
theorem permF2 : allN 8 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzInvF2.S j)
    (SuzInvF2.SI j)) = true := by quickRfl

theorem bindsF2 : Binds 1782 11 SuzInvF2.S 8 3 SuzInvF2.BP (invFullStrongArrs 2)
    (invFullBases.getD 2 []).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [invFullStrongArrs, invFullStrongCounts],
    fun j hj => ?_, by simp [invFullBases], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKF2 t ht)⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec sOKF2 j hj)
  have hk : 1 + invFullGenCounts.getD 2 0 + j = 4 + j := by simp [invFullGenCounts]
  unfold invFullStrongArrs
  rw [getElem!_pos _ j (by simpa [invFullStrongCounts] using hj), Array.getElem_ofFn]
  change invRun 2 (1 + invFullGenCounts.getD 2 0 + j) = _
  rw [hk, run_eq2 (by omega), e]
  rfl

theorem gensF2 : (invFullGenArrs 2).size = 3 ∧
    ∀ k < 3, (invFullGenArrs 2)[k]! = unpack 1782 11 (SuzInvT2.F (Nat.add 1 k)) := by
  refine ⟨by simp [invFullGenArrs, invFullGenCounts], fun k hk => ?_⟩
  unfold invFullGenArrs
  rw [getElem!_pos _ k (by simpa [invFullGenCounts] using hk), Array.getElem_ofFn]
  change invRun 2 (1 + k) = _
  rw [run_eq2 (by omega)]
  rfl

end CertificateChecks.KernelSpor.SuzInv

end
