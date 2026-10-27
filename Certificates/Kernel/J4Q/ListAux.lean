module

public import Init

public section

namespace CertificateChecks.KernelJ4Q

theorem filter_map_comm {α β : Type} {p : α → Bool} {q : β → Bool} {f : α → β} :
    ∀ (l : List α), (∀ x ∈ l, p x = q (f x)) → (l.filter p).map f = (l.map f).filter q
  | [], _ => rfl
  | x :: l, h => by
    have ih := filter_map_comm l fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.filter_cons, List.map_cons, List.filter_cons, ← h x List.mem_cons_self]
    by_cases hp : p x
    · simp only [hp, ↓reduceIte, List.map_cons, ih]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, ih]

theorem eraseDups_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β} :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
      (l.map f).eraseDups = l.eraseDups.map f
  | _, [], _, _ => rfl
  | 0, _ :: _, h, _ => absurd h (by simp)
  | n + 1, x :: l, hn, hinj => by
    rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons, List.map_cons]
    congr 1
    have hf : (l.map f).filter (fun b => !b == f x) = (l.filter fun b => !b == x).map f := by
      rw [filter_map_comm l]
      intro y hy
      by_cases e : y = x
      · subst e
        simp
      · have h2 : f y ≠ f x := fun h => e (hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self h)
        have b1 : (y == x) = false := beq_eq_false_iff_ne.2 e
        have b2 : (f y == f x) = false := beq_eq_false_iff_ne.2 h2
        rw [b1, b2]
    rw [hf]
    apply eraseDups_map_inj n
    · exact Nat.le_trans (List.length_filter_le _ _) (by simpa using hn)
    · intro a ha b hb hab
      exact hinj a (List.mem_cons_of_mem _ (List.mem_filter.1 ha).1) b
        (List.mem_cons_of_mem _ (List.mem_filter.1 hb).1) hab

end CertificateChecks.KernelJ4Q

end
