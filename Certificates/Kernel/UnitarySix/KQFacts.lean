
module

public import Certificates.Kernel.UnitarySix.KQFactsBase

public import Certificates.Kernel.UnitarySix.KQ
public import Certificates.Kernel.UnitarySix.Struct3010
public import CFSG.Certificates.Kernel.U6Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.KQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Certificates CFSG.Certificates.Native
open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

theorem arrays :
    ChainArrays kQ (SA.extract 0 3) SA kBase
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 7 kDer) := by
  have hlen : kGens.length = 3 := by simp [kGens, kWords]
  have hb := soundBinds letters_eq kWN_eq (by decide) kBinds
  refine certificate_chainArrays (gens := kGens) _ _ _ _ (by rw [hlen]; exact raw)
    (by simp [SA, hlen]) (by simp [SA, hlen]) (fun j hj => ?_) rfl (fun i => ?_)
  · rw [hlen] at hj
    have e : (SA.extract 0 3)[j]! = unpack 693 10 (S j) := by
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    rw [e]
    exact hb j (by simpa [kWords] using hj)
  · fin_cases i <;> rfl

theorem valid : ValidSchreier kQ :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem order : kQ.orderCertificate = 20160 := by
  have hv := (validSchreier_of_chainOK arrays (by norm_num) raw).2
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 3).map (fun i => rcnt (LR i)) = [21, 16, 60] := by decide
  rw [e] at hs
  have hl3 : (rawLevels 693 SA kBase).size = 3 := by simp [rawLevels, kBase]
  have hsz : ∀ i (hi : i < 3), ((rawLevels 693 SA kBase)[i]!).pts.size =
      [21, 16, 60][i]'(by simpa using hi) := by
    intro i hi
    rw [size_of_orbitSizes hs (by rw [hl3]; exact hi)]
    exact List.getD_eq_getElem _ _ _
  have hb : kQ.baseCount = 3 := rfl
  have hm : ∀ i : Fin kQ.baseCount, kQ.orbitSize i = [21, 16, 60].getD i.val 0 := fun i => by
    have hi : i.val < 3 := hb ▸ i.2
    rw [hv, hsz _ hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    rfl
  simp only [RawSchreierDatum.orderCertificate]
  rw [List.map_congr_left (fun i _ => hm i)]
  rw [show (fun i : Fin kQ.baseCount => [21, 16, 60].getD i.val 0) =
    (fun j => [21, 16, 60].getD j 0) ∘ Fin.val from rfl, ← List.map_map, hb]
  rfl

end CertificateChecks.KernelU6.KQ

end
