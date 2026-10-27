module

public import Certificates.Kernel.Sporadic.RawGenSl
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Certificates.Kernel.SporSch.RecordSound
public import CFSG.Sporadic.Co2Schreier.WitText
public meta import CFSG.Sporadic.Co2Schreier.WitText
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.TitsBasic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

@[expose] def sixC : CFSG.Monster.B.Mathieu.ChainRecord := witRec.wLocal.sixActionChain

meta def sixS : Array (Array Nat) := witRec.wLocal.sixActionChain.strongArrs

meta def sixB : Array Nat := witRec.wLocal.sixActionChain.baseArr

@[expose] def sixD : List (List Int) := sixC.derivations

end CertificateChecks.KernelSporSch.Co2M

#ks_rawchain_sl CertificateChecks.KernelSporSch.Co2Six 63 8 64 64 0
  CertificateChecks.KernelSporSch.Co2M.sixS CertificateChecks.KernelSporSch.Co2M.sixB 2
  CertificateChecks.KernelSporSch.Co2M.sixD

namespace CertificateChecks.KernelSporSch.Co2Six

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Schreier CertificateChecks.KernelSporSch.Co2M

theorem bindsOK : allN 12 (fun k => bindListK 63 8 (S k) (sixC.strongGenerators.getD k [])) = true := by
  quickRfl

theorem shapeOK : sixC.strongGenerators.length = 12 ∧ sixC.generators.length = 2 ∧
    sixC.derivations.length = 10 ∧ sixC.generators = sixC.strongGenerators.take 2 ∧
    sixC.base = [0, 1, 3, 7, 15, 31] := by
  decide +kernel

theorem baseOK : (Nat.beq sixC.baseArr.size 6 &&
    allN 6 fun t => Nat.beq sixC.baseArr[t]! (pg 8 (mask 8) BP t)) = true := by
  quickRfl

theorem perm : allN 12 (fun j => permOK 63 8 (mask 8) (63 * 8) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 63 8 S 12 6 BP sixC.strongArrs sixC.baseArr := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true hb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  · unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
    simp [shapeOK.1]
  · have e : sixC.strongArrs[j]! = (sixC.strongGenerators.getD j []).toArray := by
      unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
      rw [getElem!_pos _ j (by simp [shapeOK.1]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [shapeOK.1]; omega : j < _)]
    rw [e]
    exact toArray_eq_of_bindListK (allN_spec bindsOK j hj)

theorem record_ok : recordOK 63 sixC 4 = true :=
  recordOK_of (NS := 1) (CH := 64) shapeOK.2.2.2.1 shapeOK.2.1 (by rw [shapeOK.2.2.1]) binds
    head hl (by norm_num) hs

theorem orbits_ok : recordOrbits 63 sixC = [63, 32, 15, 8, 3, 2] := by
  rw [recordOrbits_of binds perm hl]
  decide +kernel

end CertificateChecks.KernelSporSch.Co2Six

end
