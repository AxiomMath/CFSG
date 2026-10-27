module

public import Certificates.Kernel.Sporadic.Fi24F3d.Kneser
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelFi24F3d

@[expose] def KP.Inc {n : ℕ} (i : Fin n) (p : KP n) : Prop := p.1.1 = i ∨ p.1.2 = i

instance KP.decInc {n : ℕ} (i : Fin n) : DecidablePred (KP.Inc i) := fun p => by
  unfold KP.Inc
  infer_instance

@[expose] def KP.star (i : Fin 9) : Finset (KP 9) := Finset.univ.filter (KP.Inc i)

theorem KP.not_disj_iff : ∀ p q : KP 9, ¬ KP.Disj p q ↔ ∃ i, KP.Inc i p ∧ KP.Inc i q := by
  decide

theorem KP.card_star : ∀ i : Fin 9, (KP.star i).card = 8 := by decide

theorem KP.star_injective : ∀ i j : Fin 9, KP.star i = KP.star j → i = j := by decide

theorem KP.card_inside : ∀ T : Finset (Fin 9),
    (Finset.univ.filter fun p : KP 9 => p.1.1 ∈ T ∧ p.1.2 ∈ T).card = T.card.choose 2 := by
  decide +kernel

theorem KP.card_triangle : ∀ a b c : Fin 9, a ≠ b → b ≠ c → a ≠ c →
    (Finset.univ.filter fun s : KP 9 => (KP.Inc a s ∨ KP.Inc b s) ∧ (KP.Inc b s ∨ KP.Inc c s) ∧
      (KP.Inc a s ∨ KP.Inc c s)).card ≤ 3 := by
  decide +kernel

theorem KP.star_inter : ∀ i j : Fin 9, i ≠ j → ∀ s t : KP 9, KP.Inc i s → KP.Inc j s →
    KP.Inc i t → KP.Inc j t → s = t := by
  decide

theorem KP.inc_two : ∀ t : KP 9, ∀ x y : Fin 9, x ≠ y → KP.Inc x t → KP.Inc y t →
    ∀ i, KP.Inc i t → i = x ∨ i = y := by
  decide

theorem KP.inc_fst (p : KP 9) : KP.Inc p.1.1 p := Or.inl rfl

theorem KP.inc_snd (p : KP 9) : KP.Inc p.1.2 p := Or.inr rfl

theorem KP.fst_ne_snd (p : KP 9) : p.1.1 ≠ p.1.2 := ne_of_lt p.2

theorem KP.eq_star_of_intersecting (S : Finset (KP 9)) (hS : S.card = 8)
    (hI : ∀ p ∈ S, ∀ q ∈ S, ¬ KP.Disj p q) : ∃ i, S = KP.star i := by
  classical
  obtain ⟨p, hp⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  set a := p.1.1
  set b := p.1.2
  have hab : ∀ s ∈ S, KP.Inc a s ∨ KP.Inc b s := by
    intro s hs
    obtain ⟨i, hip, his⟩ := (KP.not_disj_iff p s).1 (hI p hp s hs)
    rcases hip with h | h
    · left
      subst h
      exact his
    · right
      subst h
      exact his
  have hsub : ∀ i, (∀ s ∈ S, KP.Inc i s) → S = KP.star i := by
    intro i hi
    have h1 : S ⊆ KP.star i := fun s hs => Finset.mem_filter.2 ⟨Finset.mem_univ _, hi s hs⟩
    exact Finset.eq_of_subset_of_card_le h1 (by rw [KP.card_star, hS])
  by_cases ha : ∀ s ∈ S, KP.Inc a s
  · exact ⟨a, hsub a ha⟩
  by_cases hb : ∀ s ∈ S, KP.Inc b s
  · exact ⟨b, hsub b hb⟩
  exfalso
  push Not at ha hb
  obtain ⟨q, hq, hqa⟩ := ha
  obtain ⟨r, hr, hrb⟩ := hb
  have hqb : KP.Inc b q := (hab q hq).resolve_left hqa
  have hra : KP.Inc a r := (hab r hr).resolve_right hrb
  obtain ⟨c, hcq, hcr⟩ := (KP.not_disj_iff q r).1 (hI q hq r hr)
  have hbc : b ≠ c := fun h => hrb (by rw [h]; exact hcr)
  have hac : a ≠ c := fun h => hqa (by rw [h]; exact hcq)
  have hab' : a ≠ b := KP.fst_ne_snd p
  have meets : ∀ {x y : Fin 9} {t : KP 9}, x ≠ y → KP.Inc x t → KP.Inc y t → t ∈ S →
      ∀ s ∈ S, KP.Inc x s ∨ KP.Inc y s := by
    intro x y t hxy hx hy ht s hs
    obtain ⟨i, hit, his⟩ := (KP.not_disj_iff t s).1 (hI t ht s hs)
    rcases KP.inc_two t x y hxy hx hy i hit with rfl | rfl
    · exact Or.inl his
    · exact Or.inr his
  have hle : S ⊆ Finset.univ.filter fun s : KP 9 => (KP.Inc a s ∨ KP.Inc b s) ∧
      (KP.Inc b s ∨ KP.Inc c s) ∧ (KP.Inc a s ∨ KP.Inc c s) := fun s hs =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hab s hs, meets hbc hqb hcq hq s hs,
      meets hac hra hcr hr s hs⟩
  have := (Finset.card_le_card hle).trans (KP.card_triangle a b c hab' hbc hac)
  omega

theorem choose_two_mod5 : ∀ m ≤ 9, m % 3 = 0 → m.choose 2 % 5 ≠ 2 := by decide

theorem aut_fix_mod5 (σ : KP 9 ≃ KP 9) (hσ : ∀ p q, KP.Disj (σ p) (σ q) ↔ KP.Disj p q)
    (h3 : ∀ p, σ (σ (σ p)) = p) :
    (Finset.univ.filter fun p => σ p = p).card % 5 ≠ 2 := by
  classical
  have hstar : ∀ i, ∃ j, (KP.star i).map σ.toEmbedding = KP.star j := by
    intro i
    apply KP.eq_star_of_intersecting
    · rw [Finset.card_map, KP.card_star]
    · intro p hp q hq
      obtain ⟨p', hp', rfl⟩ := Finset.mem_map.1 hp
      obtain ⟨q', hq', rfl⟩ := Finset.mem_map.1 hq
      rw [Equiv.coe_toEmbedding, hσ, KP.not_disj_iff]
      exact ⟨i, (Finset.mem_filter.1 hp').2, (Finset.mem_filter.1 hq').2⟩
  choose π hπ using hstar
  have hinc : ∀ i p, KP.Inc i p → KP.Inc (π i) (σ p) := by
    intro i p h
    have hm : σ p ∈ KP.star (π i) := by
      rw [← hπ]
      exact Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    exact (Finset.mem_filter.1 hm).2
  have hπinj : Function.Injective π := by
    intro i j h
    apply KP.star_injective
    exact Finset.map_injective σ.toEmbedding ((hπ i).trans ((congrArg KP.star h).trans (hπ j).symm))
  have triple : ∀ s : Finset (KP 9),
      ((s.map σ.toEmbedding).map σ.toEmbedding).map σ.toEmbedding = s := by
    intro s
    ext p
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
      rw [h3]
      exact ha
    · intro hp
      exact ⟨σ (σ p), ⟨σ p, ⟨p, hp, rfl⟩, rfl⟩, h3 p⟩
  have hπ3 : ∀ i, π (π (π i)) = i := by
    intro i
    apply KP.star_injective
    rw [← hπ, ← hπ, ← hπ, triple]
  have hfix : ∀ p : KP 9, σ p = p ↔ π p.1.1 = p.1.1 ∧ π p.1.2 = p.1.2 := by
    intro p
    have hne := KP.fst_ne_snd p
    have h1 := hinc _ _ (KP.inc_fst p)
    have h2 := hinc _ _ (KP.inc_snd p)
    constructor
    · intro hp
      rw [hp] at h1 h2
      have hπne : π p.1.1 ≠ π p.1.2 := fun h => hne (hπinj h)
      rcases KP.inc_two p _ _ hne (KP.inc_fst p) (KP.inc_snd p) _ h1 with e1 | e1 <;>
        rcases KP.inc_two p _ _ hne (KP.inc_fst p) (KP.inc_snd p) _ h2 with e2 | e2
      · exact absurd (e1.trans e2.symm) hπne
      · exact ⟨e1, e2⟩
      · exfalso
        have := hπ3 p.1.1
        rw [e1, e2, e1] at this
        exact hne this.symm
      · exact absurd (e1.trans e2.symm) hπne
    · rintro ⟨e1, e2⟩
      rw [e1] at h1
      rw [e2] at h2
      exact KP.star_inter _ _ hne _ _ h1 h2 (KP.inc_fst p) (KP.inc_snd p)
  set T : Finset (Fin 9) := Finset.univ.filter fun i => π i = i with hT
  have hcard : (Finset.univ.filter fun p => σ p = p).card = T.card.choose 2 := by
    rw [← KP.card_inside T]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hT]
    exact hfix p
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let πe : Function.End (Fin 9) := π
  have hπe : πe ^ 3 ^ 1 = 1 := by
    funext i
    exact hπ3 i
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := πe) (p := 3) (n := 1) hπe
  have hTc : T.card = Fintype.card (Function.fixedPoints πe) := by
    rw [hT, ← Set.toFinset_card]
    congr 1
    ext i
    simp [Function.mem_fixedPoints, Function.IsFixedPt, πe]
  rw [hcard]
  apply choose_two_mod5 _ (by rw [hT]; exact (Finset.card_filter_le _ _).trans (by simp))
  rw [hTc]
  simp only [Fintype.card_fin] at hmod
  unfold Nat.ModEq at hmod
  omega

end CertificateChecks.KernelFi24F3d

end
