module

public import Certificates.Kernel.Multipliers.U62Rels
public import Certificates.Kernel.Misc.Coset.C10015B

public section

namespace CertificateChecks.KernelU62

open CFSG.LieType.Multipliers.U62 CFSG.CosetTable

theorem rels₁_one : ∀ r ∈ {r : FreeGroup (Fin 4) | r ∈ rels₁.map FreeGroup.mk},
    FreeGroup.lift (PresentedGroup.of : Fin 4 → PG 4 cover₁) r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  have hk' : k < 16 := by
    have : rels₁.length = 16 := by decide
    omega
  have hl : FreeGroup.lift (PresentedGroup.of : Fin 4 → PG 4 cover₁) =
      PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ cover₁.map FreeGroup.mk} :=
    FreeGroup.ext_hom _ _ fun _ => FreeGroup.lift_apply_of
  rw [hl, ← z₁_eq_one hk', z₁, List.getD_eq_getElem _ _ hk]

noncomputable def hom₁ : PG 4 rels₁ →* PG 4 cover₁ := PresentedGroup.toGroup rels₁_one

theorem hom₁_surjective : Function.Surjective hom₁ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of rels₁_one⟩

theorem cover₁_card_le : Finite (PG 4 cover₁) ∧ Nat.card (PG 4 cover₁) ≤ 13685760 := by
  obtain ⟨hf, hc⟩ := CertificateChecks.KernelMiscCoset.C10015.card_le₁
  have : Finite (PG 4 rels₁) := hf
  exact ⟨Finite.of_surjective _ hom₁_surjective,
    (Nat.card_le_card_of_surjective _ hom₁_surjective).trans hc⟩

end CertificateChecks.KernelU62

end
