module

public import CFSG.GH74.KGroups.ClassCount

public section

namespace CertificateChecks.KernelMisc.GL52K

open CFSG.GH74.KGroups

variable {G : Type*} [Group G] [Finite G]

noncomputable abbrev clsSize (r : G) : ℕ := Nat.card G / centCard (⊤ : Subgroup G) r

theorem ncard_conjSet_top (r : G) : (conjSet (⊤ : Subgroup G) r).ncard = clsSize r := by
  have h := ncard_conjSet_mul (⊤ : Subgroup G) r
  rw [Subgroup.card_top] at h
  exact (Nat.div_eq_of_eq_mul_left (centCard_pos _ r) h.symm).symm

theorem union_ncard {α : Type*} (ι : G → α) (hι : ∀ g x, ι (g * x * g⁻¹) = ι x) :
    ∀ l : List G, (l.map ι).Nodup →
      ({x | ∃ r ∈ l, x ∈ conjSet (⊤ : Subgroup G) r} : Set G).ncard = (l.map clsSize).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons r l ih =>
    intro hl
    rw [List.map_cons, List.nodup_cons] at hl
    have hs : ({x | ∃ r' ∈ r :: l, x ∈ conjSet (⊤ : Subgroup G) r'} : Set G) =
        conjSet ⊤ r ∪ {x | ∃ r' ∈ l, x ∈ conjSet (⊤ : Subgroup G) r'} := by
      ext x
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨r', rfl | hr', hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨r', hr', hx⟩
      · rintro (hx | ⟨r', hr', hx⟩)
        · exact ⟨r, Or.inl rfl, hx⟩
        · exact ⟨r', Or.inr hr', hx⟩
    have hd : Disjoint (conjSet (⊤ : Subgroup G) r)
        {x | ∃ r' ∈ l, x ∈ conjSet (⊤ : Subgroup G) r'} := by
      rw [Set.disjoint_left]
      rintro x ⟨g, -, rfl⟩ ⟨r', hr', g', -, he⟩
      apply hl.1
      refine List.mem_map.2 ⟨r', hr', ?_⟩
      rw [← hι g' r', ← he, hι]
    have hf : ({x | ∃ r' ∈ l, x ∈ conjSet (⊤ : Subgroup G) r'} : Set G).Finite := Set.toFinite _
    rw [hs, Set.ncard_union_eq hd (conjSet_finite _ r) hf, ncard_conjSet_top, ih hl.2,
      List.map_cons, List.sum_cons]

theorem card_of_classes {α : Type*} (ι : G → α) (hι : ∀ g x, ι (g * x * g⁻¹) = ι x)
    (rs : List G) (hnd : (rs.map ι).Nodup) (hsum : (rs.map clsSize).sum = Nat.card G)
    (P : G → Prop) [DecidablePred P] (hP : ∀ g x, P x → P (g * x * g⁻¹)) :
    Nat.card {x // P x} = ((rs.filter fun r => decide (P r)).map clsSize).sum := by
  have hU : ({x | ∃ r ∈ rs, x ∈ conjSet (⊤ : Subgroup G) r} : Set G) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
    rw [union_ncard ι hι rs hnd, hsum, Set.ncard_univ]
  have hnd' : ((rs.filter fun r => decide (P r)).map ι).Nodup :=
    hnd.sublist (List.Sublist.map _ List.filter_sublist)
  have hS : ({x | P x} : Set G) =
      {x | ∃ r ∈ rs.filter (fun r => decide (P r)), x ∈ conjSet (⊤ : Subgroup G) r} := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro hx
      have hxu : x ∈ ({x | ∃ r ∈ rs, x ∈ conjSet (⊤ : Subgroup G) r} : Set G) := by
        rw [hU]
        trivial
      obtain ⟨r, hr, g, -, rfl⟩ := hxu
      refine ⟨r, ⟨hr, ?_⟩, g, Subgroup.mem_top g, rfl⟩
      have := hP g⁻¹ _ hx
      rwa [show g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r by group] at this
    · rintro ⟨r, ⟨-, hr⟩, g, -, rfl⟩
      exact hP g r hr
  have e : Nat.card {x // P x} = ({x | P x} : Set G).ncard := Nat.card_coe_set_eq _
  rw [e, hS, union_ncard ι hι _ hnd']

end CertificateChecks.KernelMisc.GL52K

end
