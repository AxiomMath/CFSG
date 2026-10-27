module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def lcS : Array (Array Nat) := localRec.chains.C.strongArrs

meta def lcB : Array Nat := localRec.chains.C.baseArr

@[expose] def lcD : List (List Int) := localRec.chains.C.derivations

end CertificateChecks.KernelSporSch.Co2M

#ks_raworb CertificateChecks.KernelSporSch.Co2LC 2300 12 256
  CertificateChecks.KernelSporSch.Co2M.lcS CertificateChecks.KernelSporSch.Co2M.lcB 2
  CertificateChecks.KernelSporSch.Co2M.lcD

namespace CertificateChecks.KernelSporSch.Co2LC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Schreier

theorem bindsOK : allN 14 (fun k => bindListK 2300 12 (S k)
    (localRec.chains.C.strongGenerators.getD k [])) = true := by
  quickRfl

theorem shapeOK : localRec.chains.C.strongGenerators.length = 14 ∧
    localRec.chains.C.generators.length = 2 ∧
    localRec.chains.C.derivations.length = 12 ∧
    localRec.chains.C.generators = localRec.chains.C.strongGenerators.take 2 ∧
    localRec.chains.C.base = [0, 1, 2, 3, 4, 5] := by
  decide +kernel

theorem baseOK : (Nat.beq localRec.chains.C.baseArr.size 6 &&
    allN 6 fun t => Nat.beq localRec.chains.C.baseArr[t]! (pg 12 (mask 12) BP t)) = true := by
  quickRfl

theorem perm : allN 14 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 2300 12 S 14 6 BP localRec.chains.C.strongArrs
    localRec.chains.C.baseArr := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true hb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  · unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
    simp [shapeOK.1]
  · have e : localRec.chains.C.strongArrs[j]! =
        (localRec.chains.C.strongGenerators.getD j []).toArray := by
      unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
      rw [getElem!_pos _ j (by simp [shapeOK.1]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [shapeOK.1]; omega : j < _)]
    rw [e]
    exact toArray_eq_of_bindListK (allN_spec bindsOK j hj)

theorem orbits_ok : recordOrbits 2300 localRec.chains.C = [256, 1260, 18, 32, 2, 2] := by
  unfold recordOrbits
  rw [rawOrbitSizesK_orb binds perm ho (by norm_num)]
  decide +kernel

end CertificateChecks.KernelSporSch.Co2LC

end
