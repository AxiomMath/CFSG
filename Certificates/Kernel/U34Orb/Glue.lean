module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGenCheckInputs
public import CFSG.LieType.SeitzGeneration.HeisSmallOfMat
public import CFSG.Certificates.Kernel.U34OrbSound
public import Certificates.Kernel.U34Orb.C
import CFSG.RankThree.PartTwo.KFacts.KS21U34
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.KD.U34Orb

open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups CFSG.LieType.SeitzGeneration.HeisSmall
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 Certificates.U34Orb CFSG.KS.U34Orb

@[expose] def rho (g : unitarySU 2 2 GF16 3) : M3 GF16 :=
  ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16)

theorem rho_one : rho 1 = 1 := by
  change ofMat (1 : Matrix (Fin 3) (Fin 3) GF16) = 1
  ext <;> decide

theorem rho_mul (a b : unitarySU 2 2 GF16 3) : rho (a * b) = rho a * rho b := by
  apply toMat_injective (ι := RingHom.id GF16) (RingHom.id GF16).injective
  change toMat (RingHom.id GF16)
      (ofMat (((a * b : unitarySU 2 2 GF16 3) : GL (Fin 3) GF16) :
        Matrix (Fin 3) (Fin 3) GF16)) =
    toMat (RingHom.id GF16)
      (ofMat ((a : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) *
        ofMat ((b : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16))
  rw [toMat_id_ofMat, toMat_mul, toMat_id_ofMat, toMat_id_ofMat]
  rfl

theorem rho_injective : Function.Injective rho := by
  intro a b hab
  apply Subtype.ext
  apply Units.ext
  have h := congrArg (fun A : M3 GF16 => toMat (RingHom.id GF16) A) hab
  simpa [rho, toMat_id_ofMat] using h

theorem card_unitarySU : Nat.card (unitarySU 2 2 GF16 3) = 62400 := by
  rw [← Nat.card_congr (CFSG.LieType.Universal.Unitary.equivStatedSU
    CFSG.RankThree.PartTwo.KFacts.KS21.U34.card_GF16 3).toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.KS21.U34.card_Y

theorem iG0 : lget mI iG 0 = eM d1Mat := by decide +kernel

theorem iG1 : lget mI iG 1 = eM d2Mat := by decide +kernel

theorem oG0 : lget mI oG 0 = eM e1Mat := by decide +kernel

theorem oG1 : lget mI oG 1 = eM e2Mat := by decide +kernel

theorem eq_top_of_le {H : Subgroup (unitarySU 2 2 GF16 3)} (h : 62400 ≤ Nat.card H) : H = ⊤ := by
  have : Finite (unitarySU 2 2 GF16 3) :=
    Nat.finite_of_card_ne_zero (by rw [card_unitarySU]; norm_num)
  exact Subgroup.eq_top_of_le_card H (by rw [card_unitarySU]; exact h)

open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups CFSG.LieType.SeitzGeneration.HeisSmall
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 in
open Certificates in
theorem gen_holds :
    (∀ H : Subgroup (unitarySU 2 2 GF16 3),
      (∃ g ∈ H, ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = d1Mat) →
      (∃ g ∈ H, ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = d2Mat) → H = ⊤) ∧
    (∀ H : Subgroup (unitarySU 2 2 GF16 3),
      (∃ g ∈ H, ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = e1Mat) →
      (∃ g ∈ H, ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = e2Mat) → H = ⊤) := by
  have : Finite (unitarySU 2 2 GF16 3) :=
    Nat.finite_of_card_ne_zero (by rw [card_unitarySU]; norm_num)
  refine ⟨fun H h₁ h₂ => ?_, fun H h₁ h₂ => ?_⟩
  · obtain ⟨a, ha, hA⟩ := h₁
    obtain ⟨b, hb, hB⟩ := h₂
    have hA' : rho a = d1Mat := hA
    have hB' : rho b = d2Mat := hB
    exact eq_top_of_le (orbOK_sound rho rho_one rho_mul rho_injective H a b ha hb iG iP iT1 iS
      iQ iT2 iW (by rw [hA', iG0]) (by rw [hB', iG1]) iOK)
  · obtain ⟨a, ha, hA⟩ := h₁
    obtain ⟨b, hb, hB⟩ := h₂
    have hA' : rho a = e1Mat := hA
    have hB' : rho b = e2Mat := hB
    exact eq_top_of_le (orbOK_sound rho rho_one rho_mul rho_injective H a b ha hb oG oP oT1 oS
      oQ oT2 oW (by rw [hA', oG0]) (by rw [hB', oG1]) oOK)

end CFSG.KD.U34Orb
