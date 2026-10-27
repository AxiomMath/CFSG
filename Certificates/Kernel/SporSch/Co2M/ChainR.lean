module

public import Certificates.Kernel.SporSch.Co2M.ChainRS0
public import Certificates.Kernel.SporSch.Co2M.ChainRS1
public import Certificates.Kernel.SporSch.Co2M.ChainRS2
public import Certificates.Kernel.SporSch.Co2M.ChainRS3
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Certificates.Kernel.SporSch.RecordSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.TitsBasic

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.Co2RA

namespace CertificateChecks.KernelSporSch.Co2RA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Schreier

theorem bindsOK : allN 11 (fun k => bindListK 2048 12 (S k)
    (localRec.chains.rAction.strongGenerators.getD k [])) = true := by
  quickRfl

theorem shapeOK : localRec.chains.rAction.strongGenerators.length = 11 ∧
    localRec.chains.rAction.generators.length = 2 ∧
    localRec.chains.rAction.derivations.length = 9 ∧
    localRec.chains.rAction.generators = localRec.chains.rAction.strongGenerators.take 2 ∧
    localRec.chains.rAction.base = [3, 1, 2, 5, 8, 7, 4] := by
  decide +kernel

theorem baseOK : (Nat.beq localRec.chains.rAction.baseArr.size 7 &&
    allN 7 fun t => Nat.beq localRec.chains.rAction.baseArr[t]! (pg 12 (mask 12) BP t)) = true := by
  quickRfl

theorem perm : allN 11 (fun j => permOK 2048 12 (mask 12) (2048 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 2048 12 S 11 7 BP localRec.chains.rAction.strongArrs
    localRec.chains.rAction.baseArr := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true hb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  · unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
    simp [shapeOK.1]
  · have e : localRec.chains.rAction.strongArrs[j]! =
        (localRec.chains.rAction.strongGenerators.getD j []).toArray := by
      unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
      rw [getElem!_pos _ j (by simp [shapeOK.1]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [shapeOK.1]; omega : j < _)]
    rw [e]
    exact toArray_eq_of_bindListK (allN_spec bindsOK j hj)

theorem record_ok : recordOK 2048 localRec.chains.rAction 4 = true :=
  recordOK_of (NS := 64) (CH := 32) shapeOK.2.2.2.1 shapeOK.2.1 (by rw [shapeOK.2.2.1]) binds
    head hl (by norm_num) hs

theorem orbits_ok : recordOrbits 2048 localRec.chains.rAction = [840, 8, 6, 4, 2, 2, 2] := by
  rw [recordOrbits_of binds perm hl]
  decide +kernel

end CertificateChecks.KernelSporSch.Co2RA

end
