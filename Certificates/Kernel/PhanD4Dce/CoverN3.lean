module

public import Certificates.Kernel.PhanD4Dce.CoverNData

set_option maxRecDepth 200000

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce3

theorem brec_and_true {x y : Bool} (h : Bool.rec (motive := fun _ => Bool) false y x = true) :
    x = true ∧ y = true := by
  cases x <;> cases y
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact ⟨rfl, rfl⟩

theorem brec_and_intro {x y : Bool} (hx : x = true) (hy : y = true) :
    Bool.rec (motive := fun _ => Bool) false y x = true := by
  subst hx
  subst hy
  rfl

theorem allRange_join {P : Nat → Bool} {a : Nat} (m₁ : Nat) : ∀ {m₂ : Nat},
    CFSG.KC.TwDce2.allRange P a m₁ = true → CFSG.KC.TwDce2.allRange P (a + m₁) m₂ = true →
      CFSG.KC.TwDce2.allRange P a (m₁ + m₂) = true
  | 0, h1, _ => h1
  | m₂ + 1, h1, h2 => by
    have h2' := brec_and_true (show Bool.rec (motive := fun _ => Bool) false (P (Nat.add (a + m₁) m₂))
      (CFSG.KC.TwDce2.allRange P (a + m₁) m₂) = true from h2)
    show Bool.rec (motive := fun _ => Bool) false (P (Nat.add a (m₁ + m₂)))
      (CFSG.KC.TwDce2.allRange P a (m₁ + m₂)) = true
    refine brec_and_intro (allRange_join m₁ h1 h2'.1) ?_
    have e : Nat.add a (m₁ + m₂) = Nat.add (a + m₁) m₂ := by
      simp only [Nat.add_eq]
      omega
    rw [e]
    exact h2'.2

theorem coverN3a : coverRangeN 15 FO INVM RD RW NS 15 12 22680 16625 DS CR CA 88 17 = true := by
  decide +kernel

theorem coverN3b : coverRangeN 15 FO INVM RD RW NS 15 12 22680 16625 DS CR CA 105 16 = true := by
  decide +kernel

theorem coverN3c : coverRangeN 15 FO INVM RD RW NS 15 12 22680 16625 DS CR CA 121 16 = true := by
  decide +kernel

theorem coverN3 : coverRangeN 15 FO INVM RD RW NS 15 12 22680 16625 DS CR CA 88 49 = true :=
  allRange_join (17 + 16) (m₂ := 16) (allRange_join 17 (m₂ := 16) coverN3a coverN3b) coverN3c

end CFSG.KD.PhanD4Dce

end
