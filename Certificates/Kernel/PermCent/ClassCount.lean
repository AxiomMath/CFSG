module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union

public section

namespace CFSG.Certificates.Kernel.PkCV.ClassCount

theorem cover_two_classes {G : Type} [Group G] [DecidableEq G] (L : List G) (inv : G → Bool)
    (hnd : L.Nodup) (hmul : ∀ g h, g ∈ L → h ∈ L → g * h ∈ L) (hinv : ∀ g, g ∈ L → g⁻¹ ∈ L)
    (hconj : ∀ g x, inv (g * x * g⁻¹) = inv x) (a b : G) (ka kb : ℕ)
    (hca : (L.map fun g => g * a * g⁻¹).toFinset.card = ka)
    (hcb : (L.map fun g => g * b * g⁻¹).toFinset.card = kb)
    (hI : (L.filter inv).length = ka + kb) (hne : ka ≠ kb) (ha : a ∈ L) (hb : b ∈ L)
    (hai : inv a = true) (hbi : inv b = true) :
    ∀ t ∈ L.filter inv, ∃ g ∈ L, t = g * a * g⁻¹ ∨ t = g * b * g⁻¹ := by
  set I := L.filter inv with hIdef
  have hInd : I.Nodup := hnd.filter _
  set Ca := (L.map fun g => g * a * g⁻¹).toFinset with hCa
  set Cb := (L.map fun g => g * b * g⁻¹).toFinset with hCb
  have hsub : ∀ r, r ∈ L → inv r = true → (L.map fun g => g * r * g⁻¹).toFinset ⊆ I.toFinset := by
    intro r hr hri y hy
    rw [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    rw [List.mem_toFinset, hIdef, List.mem_filter, hconj]
    exact ⟨hmul _ _ (hmul _ _ hg hr) (hinv g hg), hri⟩
  have hdisj : Disjoint Ca Cb := by
    rw [Finset.disjoint_left]
    intro y hya hyb
    apply hne
    rw [hCa, List.mem_toFinset, List.mem_map] at hya
    rw [hCb, List.mem_toFinset, List.mem_map] at hyb
    obtain ⟨g, hg, rfl⟩ := hya
    obtain ⟨h, hh, e⟩ := hyb
    set k := h⁻¹ * g with hk
    have hkL : k ∈ L := hmul _ _ (hinv h hh) hg
    have hb' : b = k * a * k⁻¹ := by
      rw [hk]
      calc b = h⁻¹ * (h * b * h⁻¹) * h := by group
        _ = h⁻¹ * (g * a * g⁻¹) * h := by rw [e]
        _ = h⁻¹ * g * a * (h⁻¹ * g)⁻¹ := by group
    have hab : Ca = Cb := by
      ext y
      rw [hCa, hCb, List.mem_toFinset, List.mem_toFinset, List.mem_map, List.mem_map]
      constructor
      · rintro ⟨g', hg', rfl⟩
        refine ⟨g' * k⁻¹, hmul _ _ hg' (hinv k hkL), ?_⟩
        rw [hb']
        group
      · rintro ⟨h', hh', rfl⟩
        refine ⟨h' * k, hmul _ _ hh' hkL, ?_⟩
        rw [hb']
        group
    rw [← hca, ← hcb, hab]
  have hU : Ca ∪ Cb = I.toFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset (hsub a ha hai) (hsub b hb hbi))
    rw [List.toFinset_card_of_nodup hInd, hI, Finset.card_union_of_disjoint hdisj, hca, hcb]
  intro t ht
  have ht' : t ∈ Ca ∪ Cb := by rw [hU, List.mem_toFinset]; exact ht
  rcases Finset.mem_union.1 ht' with h | h
  · rw [hCa, List.mem_toFinset, List.mem_map] at h
    obtain ⟨g, hg, e⟩ := h
    exact ⟨g, hg, Or.inl e.symm⟩
  · rw [hCb, List.mem_toFinset, List.mem_map] at h
    obtain ⟨g, hg, e⟩ := h
    exact ⟨g, hg, Or.inr e.symm⟩

end CFSG.Certificates.Kernel.PkCV.ClassCount

end
