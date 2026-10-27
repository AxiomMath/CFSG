module

public import CFSG.RankThree.PartTwo.J2Residue.H2Sylow
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge

public section

namespace CertificateChecks.J2H2

open CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue.H2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable
  {ρ : ↥P →* Module.End (ZMod 2) V12}

theorem exists_cob_of_res {c : ↥P → ↥P → V12} (hc : IsNormCoc ρ c)
    (hS : ∃ b : ↥S → V12, ∀ s t : ↥S, c (incl s) (incl t) = cob (rhoS ρ) b s t) :
    ∃ β : ↥P → V12, c = cob ρ β := by
  obtain ⟨b, hb⟩ := hS
  have hodd : ∀ v : V12, Fintype.card (Fin 4725) • v = v := by
    intro v
    rw [Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (ZMod 2),
      show ((4725 : ℕ) : ZMod 2) = 1 from rfl, one_smul]
  have hres : (fun a a' : ↥Sp => c a a') = cob (ρ.comp Sp.subtype) (fun a => b (eS a)) := by
    funext a a'
    rw [← incl_eS a, ← incl_eS a', hb]
    simp only [CFSG.RankThree.PartTwo.J2Residue.H2.cob, MonoidHom.comp_apply, Subgroup.coe_subtype, rhoS, incl_eS, map_mul]
  refine ⟨tr₁ isRightTransversal ρ (fun a => b (eS a)) + compCochain isRightTransversal ρ c, ?_⟩
  funext g k
  rw [eq_tr₂_add_cob isRightTransversal ρ hodd hc g k, hres, tr₂_cob, cob_add, Pi.add_apply,
    Pi.add_apply]

open CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue in
theorem certificate111602_of_res
    (h : ∀ ρ : ↥P →* Module.End (ZMod 2) V12, IsMRep ρ → ∀ c : ↥P → ↥P → V12, IsNormCoc ρ c →
      ∃ b : ↥S → V12, ∀ s t : ↥S, c (incl s) (incl t) = cob (rhoS ρ) b s t) :
    ∀ (ρ : ↥P →* Module.End (ZMod 2) (Fin 12 → ZMod 2)),
    (∀ (j : ℕ) (v : Fin 12 → ZMod 2), ρ (letterP j) v = (C4725.Mj j).mulVec v) →
    ∀ c : ↥P → ↥P → (Fin 12 → ZMod 2), H2.IsNormCoc ρ c → ∃ β, c = H2.cob ρ β := by
  refine fun ρ hρ c hc => ?_
  exact exists_cob_of_res hc (h ρ hρ c hc)

end CertificateChecks.J2H2
