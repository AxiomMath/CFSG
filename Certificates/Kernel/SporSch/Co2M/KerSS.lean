module

public import Certificates.Kernel.Sporadic.RawGenSl
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def sS : Array (Array Nat) := localRec.chains.S.strongArrs

meta def sB : Array Nat := localRec.chains.S.baseArr

@[expose] def sD : List (List Int) := localRec.chains.S.derivations

end CertificateChecks.KernelSporSch.Co2M

#ks_rawchain_sl CertificateChecks.KernelSporSch.Co2SS 2300 12 0 128 0
  CertificateChecks.KernelSporSch.Co2M.sS CertificateChecks.KernelSporSch.Co2M.sB 15
  CertificateChecks.KernelSporSch.Co2M.sD

namespace CertificateChecks.KernelSporSch.Co2SS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native

theorem bindsOK : allN 23 (fun k => bindListK 2300 12 (S k)
    (localRec.chains.S.strongGenerators.getD k [])) = true := by
  quickRfl

theorem shapeOK : localRec.chains.S.strongGenerators.length = 23 ∧
    localRec.chains.S.base = [0, 1, 3] := by
  decide +kernel

theorem baseOK : (Nat.beq localRec.chains.S.baseArr.size 3 &&
    allN 3 fun t => Nat.beq localRec.chains.S.baseArr[t]! (pg 12 (mask 12) BP t)) = true := by
  quickRfl

theorem perm : allN 23 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 2300 12 S 23 3 BP localRec.chains.S.strongArrs localRec.chains.S.baseArr := by
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

theorem sift_of {g : Array Nat} {G : Nat} (hg : g = unpack 2300 12 G)
    (hr : allN 2300 (fun i => Nat.blt (pg 12 (mask 12) G i) 2300) = true)
    (h : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) LR TRI BP 3 0 G = true) :
    siftA 2300 levelsS localRec.chains.S.baseArr 0 g = true :=
  siftK_sound binds perm hl hg hr h

end CertificateChecks.KernelSporSch.Co2SS

end
