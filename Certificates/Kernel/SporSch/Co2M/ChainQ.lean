module

public import Certificates.Kernel.SporSch.Co2M.ChainQS
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Certificates.Kernel.SporSch.RecordSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.TitsBasic

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.Co2QA

namespace CertificateChecks.KernelSporSch.Co2QA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Schreier

theorem bindsOK : allN 17 (fun k => bindListK 512 10 (S k)
    (localRec.chains.qAction.strongGenerators.getD k [])) = true := by
  quickRfl

theorem shapeOK : localRec.chains.qAction.strongGenerators.length = 17 ∧
    localRec.chains.qAction.generators.length = 2 ∧
    localRec.chains.qAction.derivations.length = 15 ∧
    localRec.chains.qAction.generators = localRec.chains.qAction.strongGenerators.take 2 ∧
    localRec.chains.qAction.base = [1, 2, 3, 5, 4, 7, 8, 6] := by
  decide +kernel

theorem baseOK : (Nat.beq localRec.chains.qAction.baseArr.size 8 &&
    allN 8 fun t => Nat.beq localRec.chains.qAction.baseArr[t]! (pg 10 (mask 10) BP t)) = true := by
  quickRfl

theorem perm : allN 17 (fun j => permOK 512 10 (mask 10) (512 * 10) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 512 10 S 17 8 BP localRec.chains.qAction.strongArrs
    localRec.chains.qAction.baseArr := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true hb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  · unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
    simp [shapeOK.1]
  · have e : localRec.chains.qAction.strongArrs[j]! =
        (localRec.chains.qAction.strongGenerators.getD j []).toArray := by
      unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
      rw [getElem!_pos _ j (by simp [shapeOK.1]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [shapeOK.1]; omega : j < _)]
    rw [e]
    exact toArray_eq_of_bindListK (allN_spec bindsOK j hj)

theorem record_ok : recordOK 512 localRec.chains.qAction 4 = true :=
  recordOK_of (NS := 16) (CH := 32) shapeOK.2.2.2.1 shapeOK.2.1 (by rw [shapeOK.2.2.1]) binds
    head hl (by norm_num) hs

theorem orbits_ok : recordOrbits 512 localRec.chains.qAction = [270, 28, 64, 24, 4, 2, 2, 2] := by
  rw [recordOrbits_of binds perm hl]
  decide +kernel

end CertificateChecks.KernelSporSch.Co2QA

end
