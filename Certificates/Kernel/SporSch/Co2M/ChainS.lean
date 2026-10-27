module

public import Certificates.Kernel.SporSch.Co2M.ChainSS0
public import Certificates.Kernel.SporSch.Co2M.ChainSS1
public import Certificates.Kernel.SporSch.Co2M.ChainSS2
public import Certificates.Kernel.SporSch.Co2M.ChainSS3
public import Certificates.Kernel.SporSch.Co2M.ChainSS4
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Certificates.Kernel.SporSch.RecordSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.TitsBasic

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.Co2LS

namespace CertificateChecks.KernelSporSch.Co2LS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Schreier

theorem bindsOK : allN 23 (fun k => bindListK 2300 12 (S k)
    (localRec.chains.S.strongGenerators.getD k [])) = true := by
  quickRfl

theorem shapeOK : localRec.chains.S.strongGenerators.length = 23 ∧
    localRec.chains.S.generators.length = 15 ∧
    localRec.chains.S.derivations.length = 8 ∧
    localRec.chains.S.generators = localRec.chains.S.strongGenerators.take 15 ∧
    localRec.chains.S.base = [0, 1, 3] := by
  decide +kernel

theorem baseOK : (Nat.beq localRec.chains.S.baseArr.size 3 &&
    allN 3 fun t => Nat.beq localRec.chains.S.baseArr[t]! (pg 12 (mask 12) BP t)) = true := by
  quickRfl

theorem perm : allN 23 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 2300 12 S 23 3 BP localRec.chains.S.strongArrs
    localRec.chains.S.baseArr := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true hb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  · unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
    simp [shapeOK.1]
  · have e : localRec.chains.S.strongArrs[j]! =
        (localRec.chains.S.strongGenerators.getD j []).toArray := by
      unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
      rw [getElem!_pos _ j (by simp [shapeOK.1]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [shapeOK.1]; omega : j < _)]
    rw [e]
    exact toArray_eq_of_bindListK (allN_spec bindsOK j hj)

theorem record_ok : recordOK 2300 localRec.chains.S 4 = true :=
  recordOK_of (NS := 288) (CH := 8) shapeOK.2.2.2.1 shapeOK.2.1 (by rw [shapeOK.2.2.1]) binds
    head hl (by norm_num) hs

theorem orbits_ok : recordOrbits 2300 localRec.chains.S = [256, 256, 4] := by
  rw [recordOrbits_of binds perm hl]
  decide +kernel

end CertificateChecks.KernelSporSch.Co2LS

end
