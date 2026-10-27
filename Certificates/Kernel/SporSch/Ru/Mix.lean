module

public import CFSG.Sporadic.Schreier.RuMixInputs
public import Certificates.Kernel.SporSch.Ru.MixK
public import Certificates.Kernel.SporSch.Ru.LWit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuMix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuW
  CertificateChecks.KernelSporSch.RuLW

theorem mix_eq {i : Nat} (hi : i < 3) (h : prodK i = true) :
    ruMixA (prK i) = unpack 4060 12 (MK i) := by
  unfold prodK at h
  obtain ⟨hA, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hB, hM⟩ := (bAnd_iff _ _).1 h2
  have hinv : ruInv ruLGensA[0]! = unpack 4060 12 (RuW.LGI 0) := by
    rw [lg_eq (by omega)]
    exact (inv_of rfl (lgi (k := 0) (by omega))).1
  rw [ruMixA, hinv, lg_eq (by omega), y_eq hi, compEqK_sound hA, compEqK_sound hB,
    compEqK_sound hM]

theorem pow_id {i e : Nat} (h : powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) (MK i) e
    (pidn 4060 12) = true) :
    eqA 4060 (powA 4060 (unpack 4060 12 (MK i)) e) (idA 4060) = true := by
  have hp := powAppRK_sound (k := 0) (P := pidn 4060 12) (p := MK i) idA_eq h
  rw [Nat.add_zero] at hp
  rw [hp, idA_eq]
  exact RuLW.eqA_self _

open Certificates in
open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native in
theorem c15501 : eqA 4060 (powA 4060 (ruMixA 13) 7) (idA 4060) = true ∧
    eqA 4060 (ruMixA 13) (idA 4060) = false ∧
    eqA 4060 (powA 4060 (ruMixA 5) 13) (idA 4060) = true ∧
    eqA 4060 (ruMixA 5) (idA 4060) = false := by
  have e13 : ruMixA 13 = unpack 4060 12 (MK 2) := mix_eq (i := 2) (by omega) prod2
  have e5 : ruMixA 5 = unpack 4060 12 (MK 0) := mix_eq (i := 0) (by omega) prod0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e13]
    exact pow_id p13
  · rw [e13, idA_eq]
    exact neK_sound n13
  · rw [e5]
    exact pow_id p5
  · rw [e5, idA_eq]
    exact neK_sound n5

end CertificateChecks.KernelSporSch.RuMix

end
