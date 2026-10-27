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

meta def baseI2 : Array Nat := (CFSG.Sporadic.SuzOddCore.invInnerBases.getD 2 []).toArray

meta def strongI2 : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.invInnerStrongArrs 2

@[expose] def derivI2 : List (List Int) := CFSG.Sporadic.SuzOddCore.invInnerDerivations.getD 2 []

end CertificateChecks.KernelSpor.SuzInv

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzInvWI2
  "Certificates/Kernel/Sporadic/SuzInv/data/I2.json.gz" 165 10997044431770725269
  (W : List (List Nat))

#ks_rawchain_sl3g CertificateChecks.KernelSpor.SuzInvI2 1782 11 8 64 0
  CertificateChecks.KernelSpor.SuzInv.strongI2 CertificateChecks.KernelSpor.SuzInv.baseI2 2
  CertificateChecks.KernelSpor.SuzInv.derivI2 (0 2) CertificateChecks.KernelSpor.SuzInvWI2.W

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem sOKI2 : allN 6 (fun j => Nat.beq (SuzInvI2.S j) (SuzInvT2.F (Nat.add 14 j))) = true := by
  quickRfl
theorem genI2 : allN 2 (fun k => Nat.beq (SuzInvT2.F (Nat.add 12 k)) (SuzInvI2.S k)) = true := by
  quickRfl
theorem baseOKI2 : allN 3 (fun t => Nat.beq (invInnerBases.getD 2 []).toArray[t]!
    (pg 11 (mask 11) SuzInvI2.BP t)) = true := by quickRfl
theorem permI2 : allN 6 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzInvI2.S j)
    (SuzInvI2.SI j)) = true := by quickRfl

theorem bindsI2 : Binds 1782 11 SuzInvI2.S 6 3 SuzInvI2.BP (invInnerStrongArrs 2)
    (invInnerBases.getD 2 []).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [invInnerStrongArrs, invInnerStrongCounts],
    fun j hj => ?_, by simp [invInnerBases], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKI2 t ht)⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec sOKI2 j hj)
  have hk : invInnerStart 2 + invInnerGenCounts.getD 2 0 + j = 14 + j := by
    simp [invInnerStart, invInnerGenCounts, invFullGenCounts, invFullStrongCounts]
  unfold invInnerStrongArrs
  rw [getElem!_pos _ j (by simpa [invInnerStrongCounts] using hj), Array.getElem_ofFn]
  change invRun 2 (invInnerStart 2 + invInnerGenCounts.getD 2 0 + j) = _
  rw [hk, run_eq2 (by omega), e]
  rfl

theorem gensI2 : (invInnerGenArrs 2).size = 2 ∧
    ∀ k < 2, (invInnerGenArrs 2)[k]! = unpack 1782 11 (SuzInvT2.F (Nat.add 12 k)) := by
  refine ⟨by simp [invInnerGenArrs, invInnerGenCounts], fun k hk => ?_⟩
  have hs : invInnerStart 2 + k = 12 + k := by
    simp [invInnerStart, invFullGenCounts, invFullStrongCounts]
  unfold invInnerGenArrs
  rw [getElem!_pos _ k (by simpa [invInnerGenCounts] using hk), Array.getElem_ofFn]
  change invRun 2 (invInnerStart 2 + k) = _
  rw [hs, run_eq2 (by omega)]
  rfl

end CertificateChecks.KernelSpor.SuzInv

end
