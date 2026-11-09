module

public import Certificates.Kernel.Sporadic.Fi24F3d.Data
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Fi24F3d

@[expose] def cxEdge (i j : Nat) : Bool :=
  [(11, 10), (10, 0), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)].any
    fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)

@[expose] def cxMv : Nat → Nat → List Nat → Option (List Nat)
  | 0, 0, i :: j :: w => if i == j then some w else none
  | 1, 0, i :: j :: w =>
    if Nat.blt i 12 && Nat.blt j 12 && !cxEdge i j then some (j :: i :: w) else none
  | 2, 0, i :: j :: k :: w =>
    if Nat.blt i 12 && Nat.blt j 12 && cxEdge i j && i == k then some (j :: i :: j :: w) else none
  | t, p + 1, a :: w => (cxMv t p w).map (a :: ·)
  | _, _, _ => none

@[expose] def cxRun : List (Nat × Nat) → List Nat → Option (List Nat)
  | [], w => some w
  | m :: ms, w => (cxMv m.1 m.2 w).bind (cxRun ms)

@[expose] def cxOK (ms : List (Nat × Nat)) (u v : List Nat) : Bool :=
  match cxRun ms u with
  | some w => w == v
  | none => false

@[expose] def CoxRel {G : Type*} [Group G] (s : Nat → G) : Prop :=
  (∀ i, s i * s i = 1) ∧ (∀ i j, i < 12 → j < 12 → cxEdge i j = false → s i * s j = s j * s i) ∧
    ∀ i j, i < 12 → j < 12 → cxEdge i j = true → s i * s j * s i = s j * s i * s j

theorem prod_cxMv {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) (t : Nat) :
    ∀ (p : Nat) (w w' : List Nat), cxMv t p w = some w' → (w.map s).prod = (w'.map s).prod
  | 0, w, w', h => by
    match t, w, h with
    | 0, i :: j :: w, h =>
      simp only [cxMv] at h
      split at h
      · cases h
        rename_i e
        rw [beq_iff_eq] at e
        subst e
        simp [← mul_assoc, hs.1]
      · cases h
    | 1, i :: j :: w, h =>
      simp only [cxMv] at h
      split at h
      · cases h
        rename_i e
        simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at e
        obtain ⟨⟨hi, hj⟩, e⟩ := e
        simp only [List.map_cons, List.prod_cons, ← mul_assoc, hs.2.1 i j hi hj e]
      · cases h
    | 2, i :: j :: k :: w, h =>
      simp only [cxMv] at h
      split at h
      · cases h
        rename_i e
        simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at e
        obtain ⟨⟨⟨hi, hj⟩, e1⟩, rfl⟩ := e
        simp only [List.map_cons, List.prod_cons, ← mul_assoc, hs.2.2 i j hi hj e1]
      · cases h
    | 0, [], h | 0, [_], h | 1, [], h | 1, [_], h | 2, [], h | 2, [_], h | 2, [_, _], h =>
      simp [cxMv] at h
    | t + 3, w, h =>
      match w with
      | [] | [_] | [_, _] | _ :: _ :: _ :: _ => simp [cxMv] at h
  | p + 1, [], w', h => by simp [cxMv] at h
  | p + 1, a :: w, w', h => by
    simp only [cxMv, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [List.map_cons, List.prod_cons, prod_cxMv hs t p w v hv]

theorem prod_cxRun {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ∀ (ms : List (Nat × Nat)) (u v : List Nat), cxRun ms u = some v →
      (u.map s).prod = (v.map s).prod
  | [], u, v, h => by
    simp only [cxRun, Option.some.injEq] at h
    rw [h]
  | m :: ms, u, v, h => by
    simp only [cxRun, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hv⟩ := h
    rw [prod_cxMv hs m.1 m.2 u w hw, prod_cxRun hs ms w v hv]

theorem prod_of_cxOK {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) {ms : List (Nat × Nat)}
    {u v : List Nat} (h : cxOK ms u v = true) : (u.map s).prod = (v.map s).prod := by
  unfold cxOK at h
  split at h
  · rename_i w hw
    rw [beq_iff_eq] at h
    subst h
    exact prod_cxRun hs ms u w hw
  · cases h

@[expose] def MY : List (Nat × Nat) :=
  [(1, 5), (1, 6), (1, 7), (1, 8), (1, 4), (1, 5), (1, 6), (1, 3), (1, 4), (1, 2), (2, 0), (2, 2),
    (2, 4), (2, 6), (2, 8), (0, 10), (1, 9), (1, 10), (1, 11), (1, 7), (1, 8), (1, 9), (1, 5),
    (1, 6), (1, 7), (1, 3), (1, 4), (1, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 5), (2, 7), (2, 9),
    (2, 11), (0, 13), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 3), (1, 4), (1, 5),
    (1, 6), (1, 2), (1, 3), (2, 0), (1, 2), (2, 3), (1, 5), (2, 6), (1, 8), (2, 9), (1, 11),
    (0, 12), (1, 11), (1, 12), (1, 8), (1, 9), (1, 10), (1, 5), (1, 6), (1, 7), (1, 8), (1, 2),
    (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 8), (2, 10), (2, 12), (0, 14), (1, 7), (1, 8),
    (1, 9), (1, 10), (1, 5), (1, 6), (1, 7), (1, 3), (1, 4), (1, 1), (1, 2), (1, 3), (2, 4),
    (1, 6), (2, 7), (1, 9), (2, 10), (1, 12), (0, 13), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
    (1, 8), (1, 2), (1, 3), (1, 4), (2, 0), (1, 2), (1, 3), (2, 4), (1, 6), (1, 7), (2, 8),
    (1, 10), (1, 11), (0, 12), (1, 11), (1, 7), (1, 8), (1, 9), (1, 3), (1, 4), (1, 5), (1, 6),
    (1, 7), (1, 8), (2, 9), (2, 11), (0, 13), (1, 8), (1, 9), (1, 5), (1, 6), (1, 2), (1, 3),
    (1, 4), (1, 5), (2, 6), (1, 8), (2, 9), (1, 11), (0, 12), (1, 5), (1, 6), (1, 7), (1, 3),
    (1, 1), (1, 2), (2, 3), (1, 5), (1, 6), (2, 7), (1, 9), (1, 10), (0, 11), (1, 2), (1, 3),
    (1, 4), (1, 5), (2, 0), (1, 2), (1, 3), (1, 4), (2, 5), (1, 7), (1, 8), (1, 9), (0, 10),
    (1, 4), (1, 5), (1, 6), (1, 7), (2, 8), (0, 10), (1, 3), (1, 4), (1, 5), (2, 6), (1, 8),
    (0, 9), (1, 2), (1, 3), (2, 4), (1, 6), (1, 7), (0, 8), (1, 1), (2, 2), (1, 4), (1, 5),
    (1, 6), (0, 7), (2, 0), (1, 2), (1, 3), (1, 4), (1, 5), (0, 6), (0, 5), (0, 4), (0, 3),
    (0, 2), (0, 1), (0, 0)]

@[expose] def MS : List (Nat × Nat) :=
  [(1, 25), (1, 26), (1, 27), (1, 24), (1, 25), (1, 23), (2, 21), (2, 23), (2, 25), (2, 27),
    (0, 29), (0, 28), (1, 26), (0, 27), (1, 24), (1, 25), (0, 26), (1, 22), (1, 23), (1, 24),
    (0, 25), (1, 20), (1, 21), (1, 22), (1, 19), (1, 20), (1, 18), (2, 16), (2, 18), (2, 20),
    (2, 22), (0, 24), (0, 23), (1, 21), (0, 22), (1, 19), (1, 20), (0, 21), (1, 17), (1, 18),
    (1, 19), (0, 20), (1, 15), (1, 16), (1, 17), (1, 14), (1, 15), (1, 13), (2, 11), (2, 13),
    (2, 15), (2, 17), (0, 19), (0, 18), (1, 16), (0, 17), (1, 14), (1, 15), (0, 16), (1, 12),
    (1, 13), (1, 14), (0, 15), (1, 10), (1, 11), (1, 12), (1, 9), (1, 10), (1, 8), (2, 6), (2, 8),
    (2, 10), (2, 12), (0, 14), (0, 13), (1, 11), (0, 12), (1, 9), (1, 10), (0, 11), (1, 7),
    (1, 8), (1, 9), (0, 10), (1, 5), (1, 6), (1, 7), (1, 4), (1, 5), (1, 3), (2, 1), (2, 3),
    (2, 5), (2, 7), (0, 9), (0, 8), (1, 6), (0, 7), (1, 4), (1, 5), (0, 6), (1, 2), (1, 3),
    (1, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (0, 4)]

theorem M1.y7c : cxOK MY (WY ++ WY ++ WY ++ WY ++ WY ++ WY ++ WY) [] = true := by quickRfl

theorem M1.swc : cxOK MS (NS.reverse ++ WE ++ NS) WF = true := by quickRfl

theorem M1.y7 {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ((WY ++ WY ++ WY ++ WY ++ WY ++ WY ++ WY).map s).prod = 1 :=
  (prod_of_cxOK hs M1.y7c).trans (by simp)

theorem M1.sw {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ((NS.reverse ++ WE ++ NS).map s).prod = (WF.map s).prod :=
  prod_of_cxOK hs M1.swc

end CFSG.KD.Fi24F3d

end
