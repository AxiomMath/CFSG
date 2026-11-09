module

public import Certificates.Kernel.EvenSporHS.SqprodTwin

public section

namespace CertificateChecks.EvenSporHS

open CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def memR (a : R4) : List R4 → Bool :=
  List.rec (motive := fun _ => Bool) false fun x _ ih => r4eq a x || ih

@[expose] noncomputable def subL (u l : List R4) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => memR x l && ih) u

@[expose] noncomputable def eqL : List R4 → List R4 → Bool :=
  List.rec (motive := fun _ => List R4 → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false (fun b bt _ => r4eq a b && ih bt) m)

@[expose] noncomputable def stepW (u : List R4) (b : R4) (w : R4 × R4 × Bool) : Bool :=
  memR w.1 u && memR w.2.1 u &&
    r4eq (rmul (rmul w.1 w.1) (rmul w.2.1 w.2.1)) (bif w.2.2 then rneg b else b)

@[expose] noncomputable def wOK (u : List R4) : List R4 → List (R4 × R4 × Bool) → Bool :=
  List.rec (motive := fun _ => List (R4 × R4 × Bool) → Bool) (fun _ => true)
    (fun b _ ih ws => List.rec (motive := fun _ => Bool) false (fun w wt _ => stepW u b w && ih wt) ws)

theorem memR_sound {a : R4} : ∀ {l : List R4}, memR a l = true → a ∈ l
  | [], h => absurd h (by simp [memR])
  | x :: xs, h => by
    have h' : (r4eq a x || memR a xs) = true := h
    rcases Bool.or_eq_true_iff.1 h' with h1 | h1
    · rw [r4eq_iff.1 h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memR_sound h1)

theorem subL_sound {l : List R4} : ∀ {u : List R4}, subL u l = true → ∀ a ∈ u, a ∈ l
  | [], _, a, ha => absurd ha (by simp)
  | x :: xs, h, a, ha => by
    have h' : (memR x l && subL xs l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 ha with rfl | ha
    · exact memR_sound h'.1
    · exact subL_sound h'.2 a ha

theorem eqL_sound : ∀ {l m : List R4}, eqL l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [eqL])
  | _ :: _, [], h => absurd h (by simp [eqL])
  | a :: as, b :: bs, h => by
    have h' : (r4eq a b && eqL as bs) = true := h
    rw [Bool.and_eq_true] at h'
    rw [r4eq_iff.1 h'.1, eqL_sound h'.2]

theorem wOK_sound {u : List R4} : ∀ {bs : List R4} {ws : List (R4 × R4 × Bool)},
    wOK u bs ws = true → ∀ b ∈ bs, ∃ w, stepW u b w = true
  | [], _, _, b, hb => absurd hb (by simp)
  | _ :: _, [], h, _, _ => absurd h (by simp [wOK])
  | x :: xs, w :: wt, h, b, hb => by
    have h' : (stepW u x w && wOK u xs wt) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨w, h'.1⟩
    · exact wOK_sound h'.2 b hb

theorem sqprod_of_w {u q : List R4} {ws : List (R4 × R4 × Bool)} (hq : eqL q0R q = true)
    (hu : subL u q = true) (hw : wOK u q ws = true) :
    ∀ B ∈ q0List, ∃ A₁ ∈ q0List, ∃ A₂ ∈ q0List,
      B = A₁ * A₁ * (A₂ * A₂) ∨ B = -(A₁ * A₁ * (A₂ * A₂)) := by
  have hq' := eqL_sound hq
  have hroot : ∀ a, memR a u = true → ∃ A ∈ q0List, toR4 A = a := by
    intro a ha
    have h1 : a ∈ q0R := hq' ▸ subL_sound hu a (memR_sound ha)
    exact List.mem_map.1 h1
  intro B hB
  have hb : toR4 B ∈ q := hq' ▸ List.mem_map.2 ⟨B, hB, rfl⟩
  obtain ⟨⟨a₁, a₂, s⟩, hs⟩ := wOK_sound hw _ hb
  simp only [stepW, Bool.and_eq_true] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  obtain ⟨A₁, hA₁, rfl⟩ := hroot _ h1
  obtain ⟨A₂, hA₂, rfl⟩ := hroot _ h2
  have e := congrArg ofR4 (r4eq_iff.1 h3)
  rw [ofR4_rmul, ofR4_rmul, ofR4_rmul, ofR4_toR4, ofR4_toR4] at e
  refine ⟨A₁, hA₁, A₂, hA₂, ?_⟩
  cases s with
  | false =>
    rw [cond_false, ofR4_toR4] at e
    exact Or.inl e.symm
  | true =>
    rw [cond_true, ofR4_rneg (wf_toR4 B), ofR4_toR4] at e
    exact Or.inr (by rw [e, neg_neg])

end CertificateChecks.EvenSporHS
