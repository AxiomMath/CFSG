module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Set.Image

public section

namespace CertificateChecks.KernelOm2

theorem img_inv_closed {N : Nat} {S : Nat → Set Nat} {f g : Nat → Nat}
    (hS : ∀ a < N, ∀ b < N, S a = S b → a = b) (hgf : ∀ i < N, ∀ y ∈ S i, g (f y) = y)
    (hf : ∀ i < N, ∃ j < N, f '' S i = S j) : ∀ j < N, ∃ i < N, g '' S j = S i := by
  have hback : ∀ i < N, g '' (f '' S i) = S i := fun i hi => by
    rw [Set.image_image]
    exact (Set.image_congr fun y hy => hgf i hi y hy).trans (Set.image_id _)
  choose! φ hφN hφ using hf
  let F : Fin N → Fin N := fun i => ⟨φ i, hφN i i.2⟩
  have hinj : Function.Injective F := fun a b e => by
    have e' : φ a = φ b := congrArg Fin.val e
    have h2 : S a = S b := by rw [← hback a a.2, ← hback b b.2, hφ a a.2, hφ b b.2, e']
    exact Fin.ext (hS a a.2 b b.2 h2)
  intro j hj
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨j, hj⟩
  have e : φ i = j := congrArg Fin.val hi
  refine ⟨i, i.2, ?_⟩
  rw [← e, ← hφ i i.2, hback i i.2]

theorem img_word_closed {N : Nat} {S : Nat → Set Nat} (fs : List (Nat → Nat))
    (h : ∀ f ∈ fs, ∀ i < N, ∃ j < N, f '' S i = S j) :
    ∀ i < N, ∃ j < N, fs.foldr (fun f acc => f ∘ acc) id '' S i = S j := by
  induction fs with
  | nil => exact fun i hi => ⟨i, hi, Set.image_id _⟩
  | cons f fs ih =>
    intro i hi
    obtain ⟨j, hj, e⟩ := ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) i hi
    obtain ⟨k, hk, e2⟩ := h f (List.mem_cons_self ..) j hj
    refine ⟨k, hk, ?_⟩
    rw [List.foldr_cons, Set.image_comp, e, e2]

end CertificateChecks.KernelOm2

end
