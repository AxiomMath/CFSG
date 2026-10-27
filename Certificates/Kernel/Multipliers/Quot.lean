module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CertificateChecks.KernelMult

open CFSG.CosetTable

theorem card_le_mul_of_relators {m : ℕ} (R ws : List (List (Fin m × Bool))) (S : Subgroup (PG m ws))
    [S.Normal] [Finite S] [Finite (PG m R)]
    (hS : ∀ r ∈ R, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk r) ∈ S) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ Nat.card (PG m R) * Nat.card S := by
  have he : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ R.map FreeGroup.mk},
      FreeGroup.lift (fun i => (QuotientGroup.mk (PresentedGroup.of i) : PG m ws ⧸ S)) r = 1 := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    have hl : FreeGroup.lift (fun i => (QuotientGroup.mk (PresentedGroup.of i) : PG m ws ⧸ S)) =
        (QuotientGroup.mk' S).comp (PresentedGroup.mk _) :=
      FreeGroup.ext_hom _ _ fun _ => by simp [PresentedGroup.of]
    rw [hl, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hS v hv
  let f : PG m R →* PG m ws ⧸ S := PresentedGroup.toGroup he
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    induction x using PresentedGroup.induction_on with
    | H z =>
      have : (QuotientGroup.mk (PresentedGroup.mk _ z) : PG m ws ⧸ S) ∈ f.range := by
        induction z using FreeGroup.induction_on with
        | one => exact ⟨1, by simp⟩
        | of i => exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of he⟩
        | inv_of i _ =>
          refine ⟨(PresentedGroup.of i)⁻¹, ?_⟩
          rw [map_inv, PresentedGroup.toGroup.of he]
          rfl
        | mul a b ha hb =>
          rw [map_mul, QuotientGroup.mk_mul]
          exact mul_mem ha hb
      obtain ⟨x, hx⟩ := this
      exact ⟨x, hx⟩
  have hq : Finite (PG m ws ⧸ S) := Finite.of_surjective _ hf
  have hP : Finite (PG m ws) := Finite.of_subgroup_quotient S
  refine ⟨hP, ?_⟩
  rw [S.card_eq_card_quotient_mul_card_subgroup]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_surjective _ hf)

end CertificateChecks.KernelMult

end
