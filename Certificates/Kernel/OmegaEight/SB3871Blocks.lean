module

public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual

public section

namespace CertificateChecks.KernelO8.SB3871

theorem flatMap_blocks {α β : Type} (L : List (List α)) (R : List (List (List β)))
    (f : α → List β) (hlen : R.length = L.length)
    (h : ∀ s < L.length, (L.getD s []).flatMap f = (R.getD s []).flatten) :
    L.flatten.flatMap f = R.flatten.flatten := by
  rw [List.flatten_flatten, List.flatMap_def, List.map_flatten, List.flatten_flatten]
  congr 1
  refine List.ext_getElem (by simp [hlen]) fun s h1 h2 => ?_
  have hs : s < L.length := by simpa using h1
  have := h s hs
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs,
    List.getElem?_eq_getElem (hlen ▸ hs), Option.getD_some] at this
  simp only [List.getElem_map]
  rw [← List.flatMap_def, this]

theorem filter_blocks {α : Type} (L R : List (List α)) (p : α → Bool) (hlen : R.length = L.length)
    (h : ∀ s < L.length, (L.getD s []).filter p = R.getD s []) :
    L.flatten.filter p = R.flatten := by
  rw [List.filter_flatten]
  congr 1
  refine List.ext_getElem (by simp [hlen]) fun s h1 h2 => ?_
  have hs : s < L.length := by simpa using h1
  have := h s hs
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs,
    List.getElem?_eq_getElem (hlen ▸ hs), Option.getD_some] at this
  rw [List.getElem_map, this]

theorem all_blocks {α : Type} (L : List (List α)) (P : α → Bool)
    (h : ∀ s < L.length, (L.getD s []).all P = true) : L.flatten.all P = true := by
  rw [List.all_flatten, List.all_eq_true]
  intro b hb
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hb
  have := h s hs
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some] using this

end CertificateChecks.KernelO8.SB3871

end
