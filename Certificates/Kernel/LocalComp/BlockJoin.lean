module

public section

namespace CFSG.KC.Co3Bfs

theorem cover_append {f : Nat → Bool} {a b : Nat} (h1 : ∀ j < a, f j = true)
    (h2 : ∀ t < b, f (a + t) = true) : ∀ j < a + b, f j = true := by
  intro j hj
  rcases Nat.lt_or_ge j a with h | h
  · exact h1 j h
  · have := h2 (j - a) (by omega)
    rwa [Nat.add_sub_cancel' h] at this

end CFSG.KC.Co3Bfs

end
