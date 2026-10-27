module

public import Certificates.Kernel.PhanB3.SG
public import Certificates.Kernel.PhanB3.CTGlue
public import CFSG.Certificates.Kernel.Misc.Coset.ActOrbitSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelPhanB3

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration CFSG.KC.MiscCoset
  CFSG.ClassicalInvolution.Phan.Q3G

theorem ew_codes : ((CFSG.KAct.PhanB3SG.EW.map fun w => (decodeWord 8 w).map letterCode) ==
    CFSG.KAct.PhanB3SG.EW) = true := by
  decide +kernel

theorem ew_length : CFSG.KAct.PhanB3SG.EW.length = 19 := by
  decide +kernel

theorem lv_prod : (CFSG.KAct.PhanB3SG.LV.map fun l => l.2.2.length + 1).prod = 4585351680 := by
  decide +kernel

theorem map_lo8_codes (w : List (Fin 8 × Bool)) :
    (w.map fun l => (lo8 l.1, l.2)).map letterCode = w.map letterCode := by
  rw [List.map_map]
  refine List.map_congr_left fun l _ => ?_
  obtain ⟨a, b⟩ := l
  rfl

@[expose] noncomputable def sgElt (j : ℕ) : PhanB3Group :=
  if h : j < CFSG.KAct.PhanB3SG.EW.length then
    PresentedGroup.mk _ (FreeGroup.mk (decodeWord 8 CFSG.KAct.PhanB3SG.EW[j]))
  else 1

theorem chain_card (χ : PhanB3Group →* (Equiv.Perm {c : ℕ // c < 1120})ᵐᵒᵖ)
    (hχ : ∀ (w : List (Fin 8 × Bool)) (c : {c : ℕ // c < 1120}),
      ((χ (PresentedGroup.mk _ (FreeGroup.mk w))).unop c).1 =
        Act.walk CFSG.KAct.PhanB3CT.A (14 + 14)
          ((w.map fun l => (lo8 l.1, l.2)).map letterCode) c.1) :
    4585351680 ≤ Nat.card χ.range := by
  have hE := eq_of_beq ew_codes
  have hσ : ∀ c < 19, ∀ x : {c : ℕ // c < 1120},
      ((χ (sgElt c)).unop x).1 = CFSG.KAct.PhanB3SG.B (x.1 * 19 + c) := by
    intro c hc x
    have hc' : c < CFSG.KAct.PhanB3SG.EW.length := by
      rw [ew_length]
      exact hc
    have hw : (decodeWord 8 CFSG.KAct.PhanB3SG.EW[c]).map letterCode =
        CFSG.KAct.PhanB3SG.EW[c] := by
      have := congrArg (fun l => l[c]?) hE
      simpa [List.getElem?_map, List.getElem?_eq_getElem hc'] using this
    have hx := x.2
    have hr := Act.rowsOK_spec (Act.allR_spec CFSG.KAct.PhanB3SG.rows x.1 (Nat.zero_le _)
      (by omega)) c hc'
    rw [Nat.zero_add] at hr
    rw [sgElt, dif_pos hc', hχ, map_lo8_codes, hw]
    exact hr
  have := Act.le_card_range_of_levelsOK (by norm_num) hσ CFSG.KAct.PhanB3SG.LV
    CFSG.KAct.PhanB3SG.levels
  rwa [lv_prod] at this

theorem ker_facts : ∃ N : Subgroup PhanB3Group, N.Normal ∧
    Nat.card N ≤ 2 ∧
    (∀ v ∈ b3Sl3EdgeRels ++ b3Sp4EdgeRels ++ b3CtCommRels, wordVal ctElt v ∈ N) ∧
    ∀ i : Fin 8,
      (wordVal ctElt (decodeWord 6 b3PhanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ N := by
  obtain ⟨χ, h1, h2, h3⟩ := ct_facts
  refine ⟨χ.ker, inferInstance, ?_, h2, h3⟩
  obtain ⟨-, hle⟩ := card_le
  have hr := chain_card χ h1
  have hmul : Nat.card PhanB3Group = Nat.card χ.range * Nat.card χ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv]
  rw [hmul] at hle
  by_contra hk
  have h3k : 3 ≤ Nat.card χ.ker := by omega
  have := Nat.mul_le_mul hr h3k
  omega

end CertificateChecks.KernelPhanB3

end
