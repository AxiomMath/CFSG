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

meta def baseI0 : Array Nat := (CFSG.Sporadic.SuzOddCore.invInnerBases.getD 0 []).toArray

meta def strongI0 : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.invInnerStrongArrs 0

@[expose] def derivI0 : List (List Int) := CFSG.Sporadic.SuzOddCore.invInnerDerivations.getD 0 []

end CertificateChecks.KernelSpor.SuzInv

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzInvWI0
  "Certificates/Kernel/Sporadic/SuzInv/data/I0.json.gz" 1615 6532274370428331035
  (W : List (List Nat))

#ks_rawchain_sl3g CertificateChecks.KernelSpor.SuzInvI0 1782 11 8 64 0
  CertificateChecks.KernelSpor.SuzInv.strongI0 CertificateChecks.KernelSpor.SuzInv.baseI0 22
  CertificateChecks.KernelSpor.SuzInv.derivI0 (4 9) CertificateChecks.KernelSpor.SuzInvWI0.W

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem sOKI0 : allN 28 (fun j => Nat.beq (SuzInvI0.S j) (SuzInvT0.F (Nat.add 54 j))) = true := by
  quickRfl
theorem genI0 : allN 22 (fun k => Nat.beq (SuzInvT0.F (Nat.add 32 k)) (SuzInvI0.S k)) = true := by
  quickRfl
theorem baseOKI0 : allN 3 (fun t => Nat.beq (invInnerBases.getD 0 []).toArray[t]!
    (pg 11 (mask 11) SuzInvI0.BP t)) = true := by quickRfl
theorem permI0 : allN 28 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzInvI0.S j)
    (SuzInvI0.SI j)) = true := by quickRfl

theorem bindsI0 : Binds 1782 11 SuzInvI0.S 28 3 SuzInvI0.BP (invInnerStrongArrs 0)
    (invInnerBases.getD 0 []).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [invInnerStrongArrs, invInnerStrongCounts],
    fun j hj => ?_, by simp [invInnerBases], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKI0 t ht)⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec sOKI0 j hj)
  have hk : invInnerStart 0 + invInnerGenCounts.getD 0 0 + j = 54 + j := by
    simp [invInnerStart, invInnerGenCounts, invFullGenCounts, invFullStrongCounts]
  unfold invInnerStrongArrs
  rw [getElem!_pos _ j (by simpa [invInnerStrongCounts] using hj), Array.getElem_ofFn]
  change invRun 0 (invInnerStart 0 + invInnerGenCounts.getD 0 0 + j) = _
  rw [hk, run_eq0 (by omega), e]
  rfl

theorem gensI0 : (invInnerGenArrs 0).size = 22 ∧
    ∀ k < 22, (invInnerGenArrs 0)[k]! = unpack 1782 11 (SuzInvT0.F (Nat.add 32 k)) := by
  refine ⟨by simp [invInnerGenArrs, invInnerGenCounts], fun k hk => ?_⟩
  have hs : invInnerStart 0 + k = 32 + k := by
    simp [invInnerStart, invFullGenCounts, invFullStrongCounts]
  unfold invInnerGenArrs
  rw [getElem!_pos _ k (by simpa [invInnerGenCounts] using hk), Array.getElem_ofFn]
  change invRun 0 (invInnerStart 0 + k) = _
  rw [hs, run_eq0 (by omega)]
  rfl

end CertificateChecks.KernelSpor.SuzInv

end
