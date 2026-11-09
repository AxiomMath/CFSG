module

public import Certificates.Data.Kernel.M24G.Replay

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall

@[expose] def findKB (k : Nat) : KTree (Nat × Nat) → Option Nat
  | .leaf => none
  | .node l x r => bif Nat.beq k x.1 then some x.2 else bif Nat.blt k x.1 then findKB k l else findKB k r

theorem findK_eq_B (k : Nat) : ∀ t : KTree (Nat × Nat), findK k t = findKB k t
  | .leaf => rfl
  | .node l x r => by
    simp only [findK, findKB]
    rw [findK_eq_B k l, findK_eq_B k r]
    by_cases h1 : k = x.1
    · have hb : Nat.beq k x.1 = true := by rw [h1]; exact Nat.beq_refl x.1
      (rw [if_pos h1, hb]) <;> rfl
    · have hb : Nat.beq k x.1 = false := Bool.eq_false_iff.mpr fun h => h1 (Nat.eq_of_beq_eq_true h)
      by_cases h2 : k < x.1
      · have hl : Nat.blt k x.1 = true := Nat.blt_eq.mpr h2
        (rw [if_neg h1, if_pos h2, hb, hl]) <;> rfl
      · have hl : Nat.blt k x.1 = false := Bool.eq_false_iff.mpr fun h => h2 (Nat.blt_eq.mp h)
        (rw [if_neg h1, if_neg h2, hb, hl]) <;> rfl

@[expose] def insertB {α : Type} (key : α → Nat) (y : α) : KTree α → KTree α
  | .leaf => .node .leaf y .leaf
  | .node l x r => bif Nat.blt (key y) (key x) then .node (insertB key y l) x r
      else .node l x (insertB key y r)

theorem insert_eq_B {α : Type} (key : α → Nat) (y : α) :
    ∀ t : KTree α, KTree.insert key y t = insertB key y t
  | .leaf => rfl
  | .node l x r => by
    simp only [KTree.insert, insertB]
    rw [insert_eq_B key y l, insert_eq_B key y r]
    by_cases h2 : key y < key x
    · have hl : Nat.blt (key y) (key x) = true := Nat.blt_eq.mpr h2
      (rw [if_pos h2, hl]) <;> rfl
    · have hl : Nat.blt (key y) (key x) = false :=
        Bool.eq_false_iff.mpr fun h => h2 (Nat.blt_eq.mp h)
      (rw [if_neg h2, hl]) <;> rfl

@[expose] def posTreeB {α : Type} (key : α → Nat) (L : List α) : KTree (Nat × Nat) :=
  ((L.zipIdx).map fun e => (key e.1, e.2)).foldl (fun t y => insertB Prod.fst y t) .leaf

theorem posTree_eq_B {α : Type} (key : α → Nat) (L : List α) : posTree key L = posTreeB key L := by
  unfold posTree posTreeB KTree.ofList
  congr 1
  funext t y
  exact insert_eq_B Prod.fst y t

@[expose] def posAllB {α : Type} (key : α → Nat) (pos : KTree (Nat × Nat)) : List α → Nat → Bool
  | [], _ => true
  | x :: L, i => (findKB (key x) pos == some i) && posAllB key pos L (i + 1)

theorem posAll_eq_B {α : Type} (key : α → Nat) (pos : KTree (Nat × Nat)) :
    ∀ (L : List α) (i : Nat), posAll key pos L i = posAllB key pos L i
  | [], _ => rfl
  | x :: L, i => by
    simp only [posAll, posAllB, findK_eq_B, posAll_eq_B key pos L (i + 1)]

@[expose] def replayStepB {α : Type} [DecidableEq α] (key : α → Nat) (pos : KTree (Nat × Nat))
    (x : α) (h : Nat) :
    List (α → α) → Nat → List α → List Nat → List Nat → Nat →
      Option (List α × List Nat × List Nat × Nat)
  | [], _, nw, np, ng, sz => some (nw, np, ng, sz)
  | s :: ss, j, nw, np, ng, sz =>
    match findKB (key (s x)) pos with
    | none => none
    | some i =>
      if i < sz then replayStepB key pos x h ss (j + 1) nw np ng sz
      else if i = sz then
        match nw, np, ng with
        | y :: nw', p :: np', g :: ng' =>
          if y = s x ∧ p = h ∧ g = j then replayStepB key pos x h ss (j + 1) nw' np' ng' (sz + 1)
          else none
        | _, _, _ => none
      else none

theorem replayStep_eq_B {α : Type} [DecidableEq α] (key : α → Nat) (pos : KTree (Nat × Nat))
    (x : α) (h : Nat) : ∀ (ss : List (α → α)) (j : Nat) (nw : List α) (np ng : List Nat) (sz : Nat),
    replayStep key pos x h ss j nw np ng sz = replayStepB key pos x h ss j nw np ng sz
  | [], _, _, _, _, _ => rfl
  | s :: ss, j, nw, np, ng, sz => by
    have ih := replayStep_eq_B key pos x h ss
    simp only [replayStep, replayStepB, findK_eq_B, ih] <;> rfl

@[expose] def replayGoB {α : Type} [DecidableEq α] (key : α → Nat) (steps : List (α → α))
    (pos : KTree (Nat × Nat)) :
    Nat → List α → Nat → List α → List Nat → List Nat → Nat → Bool
  | 0, _, _, nw, np, ng, _ => nw.isEmpty && np.isEmpty && ng.isEmpty
  | f + 1, hs, h, nw, np, ng, sz =>
    if h < sz then
      match hs with
      | [] => false
      | x :: hs' =>
        match replayStepB key pos x h steps 0 nw np ng sz with
        | none => false
        | some (nw', np', ng', sz') => replayGoB key steps pos f hs' (h + 1) nw' np' ng' sz'
    else nw.isEmpty && np.isEmpty && ng.isEmpty

theorem replayGo_eq_B {α : Type} [DecidableEq α] (key : α → Nat) (steps : List (α → α))
    (pos : KTree (Nat × Nat)) : ∀ (f : Nat) (hs : List α) (h : Nat) (nw : List α) (np ng : List Nat)
    (sz : Nat), replayGo key steps pos f hs h nw np ng sz = replayGoB key steps pos f hs h nw np ng sz
  | 0, _, _, _, _, _, _ => rfl
  | f + 1, hs, h, nw, np, ng, sz => by
    have ih := replayGo_eq_B key steps pos f
    simp only [replayGo, replayGoB, replayStep_eq_B, ih] <;> rfl

@[expose] def replayOKB {α : Type} [DecidableEq α] (key : α → Nat) (steps : List (α → α))
    (base : α) (fuel : Nat) (L : List α) (par gen : List Nat) (pos : KTree (Nat × Nat)) : Bool :=
  (sizeK pos == L.length && posAllB key pos L 0) &&
    match L, par, gen with
    | x :: nw, p :: np, g :: ng =>
      decide (x = base) && p == 0 && g == 0 && replayGoB key steps pos fuel L 0 nw np ng 1
    | _, _, _ => false

theorem replayOK_eq_B {α : Type} [DecidableEq α] (key : α → Nat) (steps : List (α → α))
    (base : α) (fuel : Nat) (L : List α) (par gen : List Nat) (pos : KTree (Nat × Nat)) :
    replayOK key steps base fuel L par gen pos = replayOKB key steps base fuel L par gen pos := by
  simp only [replayOK, replayOKB, posOK, posAll_eq_B, replayGo_eq_B] <;> rfl

end CFSG.KC.M24G
