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

meta def baseI1 : Array Nat := (CFSG.Sporadic.SuzOddCore.invInnerBases.getD 1 []).toArray

meta def strongI1 : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.invInnerStrongArrs 1

@[expose] def derivI1 : List (List Int) := CFSG.Sporadic.SuzOddCore.invInnerDerivations.getD 1 []

end CertificateChecks.KernelSpor.SuzInv

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzInvWI1
  "Certificates/Kernel/Sporadic/SuzInv/data/I1.json.gz" 825 16289221419894532518
  (W : List (List Nat))

#ks_rawchain_sl3g CertificateChecks.KernelSpor.SuzInvI1 1782 11 8 64 0
  CertificateChecks.KernelSpor.SuzInv.strongI1 CertificateChecks.KernelSpor.SuzInv.baseI1 10
  CertificateChecks.KernelSpor.SuzInv.derivI1 (2 4) CertificateChecks.KernelSpor.SuzInvWI1.W

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore

theorem sOKI1 : allN 16 (fun j => Nat.beq (SuzInvI1.S j) (SuzInvT1.F (Nat.add 28 j))) = true := by
  quickRfl
theorem genI1 : allN 10 (fun k => Nat.beq (SuzInvT1.F (Nat.add 18 k)) (SuzInvI1.S k)) = true := by
  quickRfl
theorem baseOKI1 : allN 3 (fun t => Nat.beq (invInnerBases.getD 1 []).toArray[t]!
    (pg 11 (mask 11) SuzInvI1.BP t)) = true := by quickRfl
theorem permI1 : allN 16 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SuzInvI1.S j)
    (SuzInvI1.SI j)) = true := by quickRfl

theorem bindsI1 : Binds 1782 11 SuzInvI1.S 16 3 SuzInvI1.BP (invInnerStrongArrs 1)
    (invInnerBases.getD 1 []).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [invInnerStrongArrs, invInnerStrongCounts],
    fun j hj => ?_, by simp [invInnerBases], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKI1 t ht)⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec sOKI1 j hj)
  have hk : invInnerStart 1 + invInnerGenCounts.getD 1 0 + j = 28 + j := by
    simp [invInnerStart, invInnerGenCounts, invFullGenCounts, invFullStrongCounts]
  unfold invInnerStrongArrs
  rw [getElem!_pos _ j (by simpa [invInnerStrongCounts] using hj), Array.getElem_ofFn]
  change invRun 1 (invInnerStart 1 + invInnerGenCounts.getD 1 0 + j) = _
  rw [hk, run_eq1 (by omega), e]
  rfl

theorem gensI1 : (invInnerGenArrs 1).size = 10 ∧
    ∀ k < 10, (invInnerGenArrs 1)[k]! = unpack 1782 11 (SuzInvT1.F (Nat.add 18 k)) := by
  refine ⟨by simp [invInnerGenArrs, invInnerGenCounts], fun k hk => ?_⟩
  have hs : invInnerStart 1 + k = 18 + k := by
    simp [invInnerStart, invFullGenCounts, invFullStrongCounts]
  unfold invInnerGenArrs
  rw [getElem!_pos _ k (by simpa [invInnerGenCounts] using hk), Array.getElem_ofFn]
  change invRun 1 (invInnerStart 1 + k) = _
  rw [hs, run_eq1 (by omega)]
  rfl

end CertificateChecks.KernelSpor.SuzInv

end
