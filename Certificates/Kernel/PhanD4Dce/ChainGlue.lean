module

public import Certificates.Kernel.PhanD4Dce.Chain
public import Certificates.Kernel.PhanD4Dce.CTGlue
public import CFSG.Certificates.Kernel.Misc.Coset.ActOrbitSound

public section

set_option maxRecDepth 100000

namespace CFSG.KD.PhanD4Dce

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration CFSG.KC.MiscCoset
  CFSG.ClassicalInvolution.Phan.Q3G

theorem lv_prod : (CFSG.KAct.PhanD4Chain.LV.map fun l => l.2.2.length + 1).prod =
    4952179814400 := by
  decide +kernel

theorem chain_card (ψ : CTGroup →* (Equiv.Perm {c : ℕ // c < 1120})ᵐᵒᵖ)
    (hψ : ∀ y < 2 * 29, ∀ c : {c : ℕ // c < 1120},
      ((ψ (presLetter {r : FreeGroup (Fin 29) | r ∈ ctWs.map FreeGroup.mk} y)).unop c).1 =
        Act.step CFSG.KAct.PhanD4CT.A (29 + 29) c.1 y) :
    4952179814400 ≤ Nat.card ψ.range := by
  have hσ : ∀ c < 58, ∀ x : {c : ℕ // c < 1120},
      ((ψ (presLetter {r : FreeGroup (Fin 29) | r ∈ ctWs.map FreeGroup.mk} c)).unop x).1 =
        CFSG.KAct.PhanD4CT.A (x.1 * 58 + c) := fun c hc x => hψ c (by omega) x
  have := Act.le_card_range_of_levelsOK (by norm_num) hσ CFSG.KAct.PhanD4Chain.LV
    CFSG.KAct.PhanD4CT.levels
  rwa [lv_prod] at this

theorem ker_facts (hle : Nat.card PhanD4Group ≤ 4 * 4952179814400) :
    ∃ N : Subgroup PhanD4Group, N.Normal ∧ Nat.card N ≤ 4 ∧
      (∀ w ∈ d4CtRels, wordVal ctEltP w ∈ N) ∧
      ∀ i : Fin 8,
        (wordVal ctEltP (decodeWord 8 phanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ N := by
  obtain ⟨ψ, hψ⟩ := exists_ctAct
  let χ := ψ.comp toCT
  have hct : ∀ v ∈ d4CtRels, wordVal ctEltP v ∈ χ.ker := fun v hv => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, toCT_ct_rel hv, map_one]
  have hgen : ∀ i : Fin 8,
      (wordVal ctEltP (decodeWord 8 phanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ χ.ker :=
    fun i => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, toCT_gen i, map_one]
  refine ⟨χ.ker, inferInstance, ?_, hct, hgen⟩
  have hrange : χ.range = ψ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 toCT_surjective, ← MonoidHom.range_eq_map]
  have hr : 4952179814400 ≤ Nat.card χ.range := by
    rw [hrange]
    exact chain_card ψ hψ
  have hmul : Nat.card PhanD4Group = Nat.card χ.range * Nat.card χ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv]
  rw [hmul] at hle
  by_contra hk
  have h5 : 5 ≤ Nat.card χ.ker := by omega
  have := Nat.mul_le_mul hr h5
  omega

end CFSG.KD.PhanD4Dce

end
