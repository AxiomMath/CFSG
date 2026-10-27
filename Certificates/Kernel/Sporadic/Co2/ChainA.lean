module

public import Certificates.Kernel.Sporadic.Co2.ChainAL0a
public import Certificates.Kernel.Sporadic.Co2.ChainAL0b
public import Certificates.Kernel.Sporadic.Co2.ChainAL0c
public import Certificates.Kernel.Sporadic.Co2.ChainAL1a
public import Certificates.Kernel.Sporadic.Co2.ChainAL1b
public import Certificates.Kernel.Sporadic.Co2.ChainAL2
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Co2Cert.Data
public meta import CFSG.Sporadic.Co2Cert.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSpor.Co2A

namespace CertificateChecks.KernelSpor.Co2A

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Cert

theorem bindsOK : allN 11 (fun k =>
    bindListK 2300 12 (S k) (co2Rec.chain.strongGenerators.getD k [])) = true := by
  quickRfl

theorem lenOK : co2Rec.chain.strongGenerators.length = 11 := by
  have h : lenK (co2Rec.chain.strongGenerators.map List.length) = 11 := by
    decide +kernel
  rw [lenK_eq, List.length_map] at h
  exact h

theorem baseOK : (Nat.beq co2BaseArr.size 6 &&
    allN 6 fun t => Nat.beq co2BaseArr[t]! (pg 12 (mask 12) BP t)) = true := by
  quickRfl

theorem strong_get (k : Nat) (hk : k < 11) :
    co2StrongArrs[k]! = (co2Rec.chain.strongGenerators.getD k []).toArray := by
  unfold co2StrongArrs CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
  rw [getElem!_pos _ k (by simp [lenOK]; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lenOK]; omega : k < _)]

theorem perm : allN 11 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 2300 12 S 11 6 BP co2StrongArrs co2BaseArr := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true hb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  · unfold co2StrongArrs CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
    simp [lenOK]
  · rw [strong_get j hj]
    exact toArray_eq_of_bindListK (allN_spec bindsOK j hj)

end CertificateChecks.KernelSpor.Co2A

end
