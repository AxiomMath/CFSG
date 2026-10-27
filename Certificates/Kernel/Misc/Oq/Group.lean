
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillSignBase

public section

namespace CertificateChecks.KernelMisc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

@[expose] def OqChecks (u : Bool) : Prop :=
  oqFrom u 1 = (stabP u).map unpack6 ∧
  (∀ t, t < 64 → (∀ r ∈ repP u, r % 64 ≠ t) → oqFrom u t = []) ∧
  ((repP u).map (· % 64)).Nodup ∧
  (repP u).length = (if u then 63 else 49) ∧
  (stabP u).length = (if u then 5760 else 1152) ∧
  strictSorted ((stabP u).map fun x => codeT (unpack6 x)) = true ∧
  (∀ x ∈ repP u, validT u (unpack6 x) = true ∧ sgnOK u (unpack6 x) = true) ∧
  (∀ x ∈ stabP u, validT u (unpack6 x) = true ∧ sgnOK u (unpack6 x) = true) ∧
  (∀ r ∈ repP u, ∀ s ∈ stabP u,
    (u = true → bMul (bOf u (unpack6 r)) (bOf u (unpack6 s)) = idE →
      compT (unpack6 r) (unpack6 s) = idT ∨ compT (unpack6 r) (unpack6 s) = omT ∨
        compT (unpack6 r) (unpack6 s) = compT omT omT) ∧
    (isInvT (compT (unpack6 r) (unpack6 s)) = true →
      presT u (compT (unpack6 r) (unpack6 s)) = true →
        compT (unpack6 r) (unpack6 s) ∈ (invD u).map fun e => unpack6 e.1)) ∧
  (∀ e ∈ invD u, (∀ a ∈ e.2.1, a < 3) ∧ ∃ k, k < (killReps u).length ∧
    compT (evalW (unpack6 e.1) e.2.1) (unpack6 e.1) =
      compT ((killReps u).getD k ([], [])).1 (evalW (unpack6 e.1) e.2.1)) ∧
  (∀ k, k < (killReps u).length → validT u ((killReps u).getD k ([], [])).1 = true ∧
    ∃ c, validCert u ((killReps u).getD k ([], [])).1 c = true)

theorem exists_rep_mul {u : Bool} (hc : OqChecks u) {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) :
    ∃ r ∈ repP u, ∃ s ∈ stabP u, ∃ ρ ∈ Gq u, ∃ ς ∈ Gq u,
      tupleOf ρ = unpack6 r ∧ tupleOf ς = unpack6 s ∧ σ = ρ * ς := by
  obtain ⟨hstab, hbad, -, -, -, -, hR, -⟩ := hc
  have ht := fn_lt σ 1
  have hne : oqFrom u (fn σ 1) ≠ [] := List.ne_nil_of_mem (mem_oqFrom_fn hσ)
  have hex : ∃ r ∈ repP u, r % 64 = fn σ 1 := by
    by_contra hc
    exact hne (hbad _ ht fun r hr hrt => hc ⟨r, hr, hrt⟩)
  obtain ⟨r, hr, hrt⟩ := hex
  obtain ⟨ρ, hρ, hρt⟩ := exists_of_validT (hR r hr).1
  have hρ1 : fn ρ 1 = fn σ 1 := (fn_one_eq hρt).trans hrt
  have hς : ρ⁻¹ * σ ∈ Gq u := mul_mem (inv_mem hρ) hσ
  have hς1 : fn (ρ⁻¹ * σ) 1 = 1 := by
    rw [fn_mul _ _ (by norm_num), ← hρ1, ← fn_mul _ _ (by norm_num), inv_mul_cancel]
    rfl
  have hmem := mem_oqFrom_fn hς
  rw [hς1, hstab] at hmem
  obtain ⟨s, hs, hst⟩ := List.mem_map.1 hmem
  exact ⟨r, hr, s, hs, ρ, hρ, _, hς, hρt, hst.symm, (mul_inv_cancel_left ρ σ).symm⟩

theorem card_Gq_of {u : Bool} (hc : OqChecks u) :
    Nat.card (Gq u) = if u then 362880 else 56448 := by
  obtain ⟨hstab, -, hnd, hlR, hlS, hsort, hR, hS, -⟩ := id hc
  have hvR : ∀ r : {r // r ∈ repP u}, ∃ ρ ∈ Gq u, tupleOf ρ = unpack6 r.1 := fun r =>
    exists_of_validT (hR r.1 r.2).1
  have hvS : ∀ l : {l // l ∈ oqFrom u 1}, ∃ ς ∈ Gq u, tupleOf ς = l.1 := fun l => by
    have hl : l.1 ∈ (stabP u).map unpack6 := by
      rw [← hstab]
      exact l.2
    obtain ⟨s, hs, hsl⟩ := List.mem_map.1 hl
    rw [← hsl]
    exact exists_of_validT (hS s hs).1
  choose ρ hρ hρt using hvR
  choose ς hς hςt using hvS
  have hς1 : ∀ l, fn (ς l) 1 = 1 := fun l => by
    obtain ⟨r, hr⟩ := head_oqFrom l.2
    exact fn_of_tupleOf ((hςt l).trans hr)
  let φ : {r // r ∈ repP u} × {l // l ∈ oqFrom u 1} → Gq u := fun p =>
    ⟨ρ p.1 * ς p.2, mul_mem (hρ _) (hς _)⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun p q hpq => ?_, fun σ => ?_⟩
    · have h1 : ρ p.1 * ς p.2 = ρ q.1 * ς q.2 := congrArg Subtype.val hpq
      have hf : fn (ρ p.1) 1 = fn (ρ q.1) 1 := by
        have h2 : fn (ρ p.1 * ς p.2) 1 = fn (ρ q.1 * ς q.2) 1 := by rw [h1]
        rwa [fn_mul _ _ (by norm_num), fn_mul _ _ (by norm_num), hς1, hς1] at h2
      rw [fn_one_eq (hρt _), fn_one_eq (hρt _)] at hf
      have hr : p.1 = q.1 := Subtype.ext (List.inj_on_of_nodup_map hnd p.1.2 q.1.2 hf)
      have h2 : ς p.2 = ς q.2 := by
        rw [hr] at h1
        exact mul_left_cancel h1
      have h3 := congrArg tupleOf h2
      rw [hςt, hςt] at h3
      exact Prod.ext hr (Subtype.ext h3)
    · obtain ⟨r, hr, s, hs, ρ', hρ', ς', hς', hρ't, hς't, he⟩ := exists_rep_mul hc σ.2
      have hl : unpack6 s ∈ oqFrom u 1 := by
        rw [hstab]
        exact List.mem_map.2 ⟨s, hs, rfl⟩
      refine ⟨(⟨r, hr⟩, ⟨unpack6 s, hl⟩), Subtype.ext ?_⟩
      change ρ ⟨r, hr⟩ * ς ⟨unpack6 s, hl⟩ = σ.1
      rw [he, tupleOf_injective (hρ _).1 hρ'.1 ((hρt _).trans hρ't.symm),
        tupleOf_injective (hς _).1 hς'.1 ((hςt _).trans hς't.symm)]
  have hndS : (oqFrom u 1).Nodup := by
    rw [hstab]
    refine List.Nodup.of_map codeT ?_
    rw [List.map_map]
    exact (strictSorted_pairwise _ hsort).nodup
  rw [← Nat.card_congr (Equiv.ofBijective φ hbij), Nat.card_prod,
    card_mem_list (List.Nodup.of_map (· % 64) hnd), card_mem_list hndS, hlR, hstab,
    List.length_map, hlS]
  cases u <;> rfl

theorem facts_of_checks {u : Bool} (hc : OqChecks u) :
    Nat.card (Gq u) = (if u then 362880 else 56448) ∧
    (∀ σ ∈ Gq u, sgnOK u (tupleOf σ) = true) ∧
    (∀ σ ∈ Gq u, u = true → bOf u (tupleOf σ) = idE →
      tupleOf σ = idT ∨ tupleOf σ = omT ∨ tupleOf σ = compT omT omT) ∧
    (∀ σ ∈ Gq u, isInvT (tupleOf σ) = true → presT u (tupleOf σ) = true →
      ∃ w, (∀ a ∈ w, a < 3) ∧ ∃ k, k < (killReps u).length ∧
        compT (evalW (tupleOf σ) w) (tupleOf σ) =
          compT ((killReps u).getD k ([], [])).1 (evalW (tupleOf σ) w)) ∧
    (∀ k, k < (killReps u).length → validT u ((killReps u).getD k ([], [])).1 = true ∧
      ∃ c, validCert u ((killReps u).getD k ([], [])).1 c = true) := by
  refine ⟨card_Gq_of hc, fun σ hσ => ?_, fun σ hσ hu hB => ?_, fun σ hσ hinv hp => ?_,
    hc.2.2.2.2.2.2.2.2.2.2⟩
  · obtain ⟨r, hr, s, hs, ρ, hρ, ς, hς, hρt, hςt, rfl⟩ := exists_rep_mul hc hσ
    obtain ⟨-, -, -, -, -, -, hR, hS, -⟩ := hc
    refine sgnOK_mul hρ hς ?_ ?_
    · rw [hρt]
      exact (hR r hr).2
    · rw [hςt]
      exact (hS s hs).2
  · obtain ⟨r, hr, s, hs, ρ, hρ, ς, hς, hρt, hςt, rfl⟩ := exists_rep_mul hc hσ
    obtain ⟨-, -, -, -, -, -, -, -, hel, -⟩ := hc
    rw [bOf_mul hρ hς, hρt, hςt] at hB
    rw [tupleOf_mul hρ.1, hρt, hςt]
    exact (hel r hr s hs).1 hu hB
  · obtain ⟨r, hr, s, hs, ρ, hρ, ς, hς, hρt, hςt, rfl⟩ := exists_rep_mul hc hσ
    obtain ⟨-, -, -, -, -, -, -, -, hel, hconj, -⟩ := hc
    rw [tupleOf_mul hρ.1, hρt, hςt] at hinv hp ⊢
    obtain ⟨e, he, hel'⟩ := List.mem_map.1 ((hel r hr s hs).2 hinv hp)
    change unpack6 e.1 = _ at hel'
    obtain ⟨h3, k, hk, heq⟩ := hconj e he
    rw [hel'] at heq
    exact ⟨e.2.1, h3, k, hk, heq⟩

end CertificateChecks.KernelMisc.Oq
