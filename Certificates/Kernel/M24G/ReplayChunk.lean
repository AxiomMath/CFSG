module

public import Certificates.Kernel.M24G.ReplayB

public section

namespace CFSG.KC.M24G.ReplayQ

open CFSG.KC.M24G CFSG.KC.ONanSmall

@[expose] def listBeqQ : List Nat → List Nat → Bool
  | [], [] => true
  | a :: l, b :: m => Nat.beq a b && listBeqQ l m
  | _, _ => false

theorem listBeqQ_iff : ∀ l m : List Nat, listBeqQ l m = true ↔ l = m
  | [], [] => by simp [listBeqQ]
  | [], _ :: _ => by simp [listBeqQ]
  | _ :: _, [] => by simp [listBeqQ]
  | a :: l, b :: m => by
    have hab : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩
    simp only [listBeqQ, Bool.and_eq_true, hab, listBeqQ_iff l m, List.cons.injEq]

@[expose] def decEqLQ : DecidableEq (List Nat) := fun a b =>
  decidable_of_iff (listBeqQ a b = true) (listBeqQ_iff _ _)

@[expose] def decEqQ : DecidableEq (Array Nat) := fun a b =>
  decidable_of_iff (listBeqQ a.toList b.toList = true) ((listBeqQ_iff _ _).trans Array.toList_inj)

@[expose] def balK : Nat → Nat → List (Nat × Nat) → KTree (Nat × Nat) × List (Nat × Nat)
  | 0, _, l => (.leaf, l)
  | d + 1, n, l =>
    bif Nat.beq n 0 then (.leaf, l) else
      match balK d (Nat.div (n - 1) 2) l with
      | (lt, x :: l1) =>
        match balK d (n - 1 - Nat.div (n - 1) 2) l1 with
        | (rt, l2) => (.node lt x rt, l2)
      | (lt, []) => (lt, [])

theorem replayOKB_inst {α : Type} (i j : DecidableEq α) (key : α → Nat) (steps : List (α → α))
    (base : α) (fuel : Nat) (L : List α) (par gen : List Nat) (pos : KTree (Nat × Nat)) :
    @replayOKB _ i key steps base fuel L par gen pos =
      @replayOKB _ j key steps base fuel L par gen pos := by
  rw [Subsingleton.elim i j]

section Chunks

variable {α : Type} [DecidableEq α] (key : α → Nat) (steps : List (α → α)) (pos : KTree (Nat × Nat))

@[expose] def replayRunB :
    Nat → List α → Nat → List α → List Nat → List Nat → Nat →
      Option (List α × Nat × List α × List Nat × List Nat × Nat)
  | 0, hs, h, nw, np, ng, sz => some (hs, h, nw, np, ng, sz)
  | f + 1, hs, h, nw, np, ng, sz =>
    if h < sz then
      match hs with
      | [] => none
      | x :: hs' =>
        match replayStepB key pos x h steps 0 nw np ng sz with
        | none => none
        | some (nw', np', ng', sz') => replayRunB f hs' (h + 1) nw' np' ng' sz'
    else none

theorem replayStepB_drop (x : α) (h : Nat) : ∀ (ss : List (α → α)) (j : Nat) (nw : List α)
    (np ng : List Nat) (sz : Nat) (nw' : List α) (np' ng' : List Nat) (sz' : Nat),
    replayStepB key pos x h ss j nw np ng sz = some (nw', np', ng', sz') →
      ∃ k, nw' = nw.drop k ∧ np' = np.drop k ∧ ng' = ng.drop k ∧ sz' = sz + k
  | [], _, nw, np, ng, sz, _, _, _, _, e => by
    simp only [replayStepB, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    exact ⟨0, rfl, rfl, rfl, rfl⟩
  | s :: ss, j, nw, np, ng, sz, nw', np', ng', sz', e => by
    simp only [replayStepB] at e
    cases hf : findKB (key (s x)) pos with
    | none => rw [hf] at e; cases e
    | some i =>
      rw [hf] at e
      simp only at e
      by_cases h1 : i < sz
      · simp only [h1, ↓reduceIte] at e
        exact replayStepB_drop x h ss _ _ _ _ _ _ _ _ _ e
      · simp only [h1, ↓reduceIte] at e
        by_cases h2 : i = sz
        · simp only [h2, ↓reduceIte] at e
          rcases nw with _ | ⟨y, nw0⟩ <;> rcases np with _ | ⟨p, np0⟩ <;>
            rcases ng with _ | ⟨g, ng0⟩ <;> try (simp at e; done)
          simp only at e
          by_cases h3 : y = s x ∧ p = h ∧ g = j
          · simp only [h3, and_self, ↓reduceIte] at e
            obtain ⟨k, e1, e2, e3, e4⟩ := replayStepB_drop x h ss _ _ _ _ _ _ _ _ _ e
            exact ⟨k + 1, e1, e2, e3, by omega⟩
          · simp only [h3, ↓reduceIte] at e
            cases e
        · simp only [h2, ↓reduceIte] at e
          cases e

theorem replayRunB_spec (g : Nat) : ∀ (f : Nat) (hs : List α) (h : Nat) (nw : List α)
    (np ng : List Nat) (sz : Nat) (hs' : List α) (h' : Nat) (nw' : List α) (np' ng' : List Nat)
    (sz' : Nat), replayRunB key steps pos f hs h nw np ng sz = some (hs', h', nw', np', ng', sz') →
      replayGoB key steps pos (f + g) hs h nw np ng sz =
        replayGoB key steps pos g hs' h' nw' np' ng' sz' ∧
      ∃ k m, hs' = hs.drop k ∧ h' = h + k ∧ nw' = nw.drop m ∧ np' = np.drop m ∧
        ng' = ng.drop m ∧ sz' = sz + m
  | 0, hs, h, nw, np, ng, sz, _, _, _, _, _, _, e => by
    simp only [replayRunB, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := e
    exact ⟨by rw [Nat.zero_add], 0, 0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | f + 1, hs, h, nw, np, ng, sz, hs', h', nw', np', ng', sz', e => by
    have hfg : f + 1 + g = (f + g) + 1 := by omega
    rw [hfg]
    simp only [replayRunB] at e
    by_cases hlt : h < sz
    · simp only [hlt, ↓reduceIte] at e
      rcases hs with _ | ⟨x, hs0⟩
      · cases e
      simp only at e
      cases hst : replayStepB key pos x h steps 0 nw np ng sz with
      | none => rw [hst] at e; cases e
      | some r =>
        obtain ⟨nw1, np1, ng1, sz1⟩ := r
        rw [hst] at e
        simp only at e
        obtain ⟨k1, d1, d2, d3, d4⟩ := replayStepB_drop key pos x h steps 0 nw np ng sz _ _ _ _ hst
        obtain ⟨hgo, k, m, e1, e2, e3, e4, e5, e6⟩ :=
          replayRunB_spec g f hs0 (h + 1) nw1 np1 ng1 sz1 _ _ _ _ _ _ e
        have hstep : replayGoB key steps pos (f + g + 1) (x :: hs0) h nw np ng sz =
            replayGoB key steps pos (f + g) hs0 (h + 1) nw1 np1 ng1 sz1 := by
          rw [replayGoB.eq_def]
          simp only [hlt, hst, ↓reduceIte]
        refine ⟨hstep.trans hgo, k + 1, k1 + m, e1, by omega, ?_, ?_, ?_, by omega⟩
        · rw [e3, d1, List.drop_drop]
        · rw [e4, d2, List.drop_drop]
        · rw [e5, d3, List.drop_drop]
    · simp only [hlt, ↓reduceIte] at e
      cases e

@[expose] def chunkB (L : List α) (par gen : List Nat) (f a b a' b' : Nat) : Bool :=
  match replayRunB key steps pos f (L.drop a) a (L.drop b) (par.drop b) (gen.drop b) b with
  | some (_, h', _, _, _, sz') => Nat.beq h' a' && Nat.beq sz' b'
  | none => false

theorem replayGoB_chunk {key : α → Nat} {steps : List (α → α)} {pos : KTree (Nat × Nat)}
    {L : List α} {par gen : List Nat} {f a b a' b' : Nat}
    (hc : chunkB key steps pos L par gen f a b a' b' = true) (g : Nat) :
    replayGoB key steps pos (f + g) (L.drop a) a (L.drop b) (par.drop b) (gen.drop b) b =
      replayGoB key steps pos g (L.drop a') a' (L.drop b') (par.drop b') (gen.drop b') b' := by
  unfold chunkB at hc
  cases hr : replayRunB key steps pos f (L.drop a) a (L.drop b) (par.drop b) (gen.drop b) b with
  | none => rw [hr] at hc; cases hc
  | some r =>
    obtain ⟨hs', h', nw', np', ng', sz'⟩ := r
    rw [hr] at hc
    simp only [Bool.and_eq_true, Nat.beq_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨hgo, k, m, e1, e2, e3, e4, e5, e6⟩ :=
      replayRunB_spec key steps pos g f _ _ _ _ _ _ _ _ _ _ _ _ hr
    rw [hgo, e1, e3, e4, e5, e2, e6, List.drop_drop, List.drop_drop, List.drop_drop,
      List.drop_drop]

@[expose] def posAllN : Nat → List α → Nat → Bool
  | 0, _, _ => true
  | _ + 1, [], _ => true
  | n + 1, x :: L, i => (findKB (key x) pos == some i) && posAllN n L (i + 1)

omit [DecidableEq α] in
theorem posAllB_of_N : ∀ (n : Nat) (l : List α) (i : Nat), posAllN key pos n l i = true →
    posAllB key pos (l.drop n) (i + n) = true → posAllB key pos l i = true
  | 0, _, _, _, h2 => h2
  | _ + 1, [], _, _, _ => rfl
  | n + 1, x :: l, i, h1, h2 => by
    simp only [posAllN, Bool.and_eq_true] at h1
    simp only [posAllB, Bool.and_eq_true]
    refine ⟨h1.1, posAllB_of_N n l (i + 1) h1.2 ?_⟩
    have hi : i + 1 + n = i + (n + 1) := by omega
    rw [hi]
    exact h2

omit [DecidableEq α] in
theorem posAllB_chunk {key : α → Nat} {pos : KTree (Nat × Nat)} {L : List α} {n a : Nat}
    (h1 : posAllN key pos n (L.drop a) a = true)
    (h2 : posAllB key pos (L.drop (a + n)) (a + n) = true) :
    posAllB key pos (L.drop a) a = true := by
  refine posAllB_of_N key pos n _ a h1 ?_
  rw [List.drop_drop]
  exact h2

@[expose] def headB (base : α) : List α → List Nat → List Nat → Bool
  | x :: _, p :: _, g :: _ => decide (x = base) && p == 0 && g == 0
  | _, _, _ => false

theorem replayOKB_of {key : α → Nat} {steps : List (α → α)} {pos : KTree (Nat × Nat)}
    {base : α} {fuel : Nat} {L : List α} {par gen : List Nat}
    (hsz : (sizeK pos == L.length) = true) (hpos : posAllB key pos (L.drop 0) 0 = true)
    (hhd : headB base L par gen = true)
    (hgo : replayGoB key steps pos fuel (L.drop 0) 0 (L.drop 1) (par.drop 1) (gen.drop 1) 1 = true) :
    replayOKB key steps base fuel L par gen pos = true := by
  rw [List.drop_zero] at hpos hgo
  unfold replayOKB
  rw [hsz, hpos]
  rcases L with _ | ⟨x, nw⟩ <;> rcases par with _ | ⟨p, np⟩ <;> rcases gen with _ | ⟨g, ng⟩ <;>
    try (simp [headB] at hhd; done)
  simp only [headB] at hhd
  simp only [List.drop_succ_cons, List.drop_zero] at hgo
  simp only [hhd, hgo, Bool.and_true]

end Chunks

end CFSG.KC.M24G.ReplayQ
