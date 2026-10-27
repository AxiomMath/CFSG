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

meta def ldS : Array (Array Nat) := localRec.chains.D.strongArrs

meta def ldB : Array Nat := localRec.chains.D.baseArr

@[expose] def ldD : List (List Int) := localRec.chains.D.derivations

end CertificateChecks.KernelSporSch.Co2M

#ks_raworb CertificateChecks.KernelSporSch.Co2LD 2300 12 256
  CertificateChecks.KernelSporSch.Co2M.ldS CertificateChecks.KernelSporSch.Co2M.ldB 2
  CertificateChecks.KernelSporSch.Co2M.ldD

namespace CertificateChecks.KernelSporSch.Co2LD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Schreier

theorem bindsOK : allN 12 (fun k => bindListK 2300 12 (S k)
    (localRec.chains.D.strongGenerators.getD k [])) = true := by
  quickRfl

theorem shapeOK : localRec.chains.D.strongGenerators.length = 12 ∧
    localRec.chains.D.generators.length = 2 ∧
    localRec.chains.D.derivations.length = 10 ∧
    localRec.chains.D.generators = localRec.chains.D.strongGenerators.take 2 ∧
    localRec.chains.D.base = [1, 2, 0, 3] := by
  decide +kernel

theorem baseOK : (Nat.beq localRec.chains.D.baseArr.size 4 &&
    allN 4 fun t => Nat.beq localRec.chains.D.baseArr[t]! (pg 12 (mask 12) BP t)) = true := by
  quickRfl

theorem perm : allN 12 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 2300 12 S 12 4 BP localRec.chains.D.strongArrs
    localRec.chains.D.baseArr := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true hb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  · unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
    simp [shapeOK.1]
  · have e : localRec.chains.D.strongArrs[j]! =
        (localRec.chains.D.strongGenerators.getD j []).toArray := by
      unfold CFSG.Monster.B.Mathieu.ChainRecord.strongArrs
      rw [getElem!_pos _ j (by simp [shapeOK.1]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [shapeOK.1]; omega : j < _)]
    rw [e]
    exact toArray_eq_of_bindListK (allN_spec bindsOK j hj)

theorem orbits_ok : recordOrbits 2300 localRec.chains.D = [1920, 56, 96, 4] := by
  unfold recordOrbits
  rw [rawOrbitSizesK_orb binds perm ho (by norm_num)]
  decide +kernel

end CertificateChecks.KernelSporSch.Co2LD

end
