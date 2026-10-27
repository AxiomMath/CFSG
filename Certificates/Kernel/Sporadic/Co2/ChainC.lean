module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Co2Cert.Data
public meta import CFSG.Sporadic.Co2Cert.Data
import CFSG.Certificates.Kernel.Common.Harness
public meta import Mathlib.GroupTheory.Schreier

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2

@[expose] def derivC : List (List Int) := CFSG.Sporadic.Co2Cert.co2Rec.coprimeChain.derivations

end CertificateChecks.KernelSpor.Co2

#ks_raworb CertificateChecks.KernelSpor.Co2C 2300 12 16
  CFSG.Sporadic.Co2Cert.co2cStrongArrs CFSG.Sporadic.Co2Cert.co2cBaseArr 2
  CertificateChecks.KernelSpor.Co2.derivC

namespace CertificateChecks.KernelSpor.Co2C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Cert

theorem bindsOK : allN 17 (fun k =>
    bindListK 2300 12 (S k) (co2Rec.coprimeChain.strongGenerators.getD k [])) = true := by
  quickRfl

theorem lenOK : co2Rec.coprimeChain.strongGenerators.length = 17 := by
  have h : lenK (co2Rec.coprimeChain.strongGenerators.map List.length) = 17 := by
    decide +kernel
  rw [lenK_eq, List.length_map] at h
  exact h

theorem baseOK : (Nat.beq co2cBaseArr.size 6 &&
    allN 6 fun t => Nat.beq co2cBaseArr[t]! (pg 12 (mask 12) BP t)) = true := by
  quickRfl

theorem strong_get (k : Nat) (hk : k < 17) :
    co2cStrongArrs[k]! = (co2Rec.coprimeChain.strongGenerators.getD k []).toArray := by
  unfold co2cStrongArrs CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
  rw [getElem!_pos _ k (by simp [lenOK]; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lenOK]; omega : k < _)]

theorem perm : allN 17 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 2300 12 S 17 6 BP co2cStrongArrs co2cBaseArr := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true hb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  · unfold co2cStrongArrs CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
    simp [lenOK]
  · rw [strong_get j hj]
    exact toArray_eq_of_bindListK (allN_spec bindsOK j hj)

end CertificateChecks.KernelSpor.Co2C

end
