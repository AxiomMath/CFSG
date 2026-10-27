module

public import Certificates.Kernel.Fi23K.Bound
public import CFSG.Certificates.Kernel.Spor.PChainLower

public section

namespace CFSG.KD.Fi23K

open CFSG.KC.Fi23K CFSG.KS.PC CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native TauCeti

noncomputable abbrev T23 : Subgroup (Equiv.Perm (Fin 31671)) := grp 31671 24 (chainLetters orbLit)

theorem card_T23_ge : 4089470473293004800 ≤ Nat.card T23 := by
  have h := card_ge chain_hyp (by norm_num)
  rwa [prod_cnt] at h

theorem T23_le : T23 ≤ Xc := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, rfl⟩
  exact letter_mem l.isLt

theorem grp_eq : T23 = Xc :=
  Subgroup.eq_of_le_of_card_ge T23_le (card_Xc.trans card_T23_ge)

theorem card_Xc_eq : Nat.card Xc = 4089470473293004800 :=
  le_antisymm card_Xc (card_T23_ge.trans (Subgroup.card_le_of_le T23_le))

theorem phiX_injective : Function.Injective phiX := by
  obtain ⟨hf, hc⟩ := CFSG.Sporadic.Presentation.Fi23.finite_card_le
  have hf' : Finite (PresentedGroup P23.relatorSet) := hf
  have hsurj := phiX.rangeRestrict_surjective
  have hcard : Nat.card phiX.range = Nat.card (PresentedGroup P23.relatorSet) := by
    refine le_antisymm (Nat.card_le_card_of_surjective _ hsurj) ?_
    rw [range_phiX, card_Xc_eq]
    exact hc
  have hbij := (Function.Surjective.bijective_of_nat_card_le hsurj (le_of_eq hcard.symm))
  intro a b e
  exact hbij.1 (Subtype.ext e)

end CFSG.KD.Fi23K

end
