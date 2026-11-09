module

public import Certificates.Data.Kernel.TWDK

public section

namespace Certificates.TWDK

open Certificates.DepASmall

@[expose] def kResT (p N : Nat) (F : List GGDepANPair) (pos : Nat) (sw ra : List KWit)
    (o : GGDepANPair) (e : Nat × List Nat) : Bool :=
  if e.1 = 0 then kAll2 (fun c i => kTest p N F [o, c] (ra.getD i kW0)) (kInner p N pos o) e.2
  else kTest p N F [o] (sw.getD (e.1 - 1) kW0)

theorem kRes_eq (p N : Nat) (F : List GGDepANPair) (key : Nat × Nat) (sw ra : List KWit)
    (ent : List (Nat × List Nat)) :
    kRes p N F key sw ra ent = kAll2 (kResT p N F key.1 sw ra) (kOuter p N key.1 key.2) ent :=
  rfl

@[expose] def kResPart (p N : Nat) (F : List GGDepANPair) (R : List KResE) (i a b : Nat) : Bool :=
  match R[i]? with
  | some e => kAll2 (kResT p N F e.1.1 e.2.1 e.2.2.1)
      (((kOuter p N e.1.1 e.1.2).drop a).take b) ((e.2.2.2.drop a).take b)
  | none => false

@[expose] def kResTail (p N : Nat) (F : List GGDepANPair) (R : List KResE) (i a : Nat) : Bool :=
  match R[i]? with
  | some e => kAll2 (kResT p N F e.1.1 e.2.1 e.2.2.1)
      ((kOuter p N e.1.1 e.1.2).drop a) (e.2.2.2.drop a)
  | none => false

theorem kAll2_take_drop {α β : Type} (t : α → β → Bool) :
    ∀ (m : Nat) (xs : List α) (ys : List β),
      kAll2 t xs ys = (kAll2 t (xs.take m) (ys.take m) && kAll2 t (xs.drop m) (ys.drop m))
  | 0, xs, ys => by simp [kAll2]
  | _ + 1, [], [] => rfl
  | _ + 1, [], _ :: _ => rfl
  | _ + 1, _ :: _, [] => rfl
  | m + 1, x :: xs, y :: ys => by
    simp only [kAll2, List.take_succ_cons, List.drop_succ_cons]
    rw [kAll2_take_drop t m xs ys, Bool.and_assoc]

theorem kAll2_of_parts {α β : Type} (t : α → β → Bool) (xs : List α) (ys : List β) (m b : Nat)
    (h : ∀ j < m, kAll2 t ((xs.drop (j * b)).take b) ((ys.drop (j * b)).take b) = true)
    (ht : kAll2 t (xs.drop (m * b)) (ys.drop (m * b)) = true) : kAll2 t xs ys = true := by
  have key : ∀ j, j ≤ m → kAll2 t (xs.drop ((m - j) * b)) (ys.drop ((m - j) * b)) = true := by
    intro j
    induction j with
    | zero => intro _; simpa using ht
    | succ j ih =>
      intro hj
      have hp := h (m - (j + 1)) (by omega)
      have e : (m - j) * b = (m - (j + 1)) * b + b := by
        rw [← Nat.succ_mul]; congr 1; omega
      rw [kAll2_take_drop t b, List.drop_drop, List.drop_drop, ← e, hp, ih (by omega)]
      rfl
  simpa using key m (Nat.le_refl m)

theorem kResAt_of_parts (p N : Nat) (F : List GGDepANPair) (R : List KResE) (i m b : Nat)
    (h : ∀ j < m, kResPart p N F R i (j * b) b = true)
    (ht : kResTail p N F R i (m * b) = true) : kResAt p N F R i = true := by
  unfold kResAt
  unfold kResPart at h
  unfold kResTail at ht
  cases hR : R[i]? with
  | none => rw [hR] at ht; exact absurd ht Bool.false_ne_true
  | some e =>
    simp only [hR] at h ht
    show kRes p N F e.1 e.2.1 e.2.2.1 e.2.2.2 = true
    rw [kRes_eq]
    exact kAll2_of_parts _ _ _ m b h ht

end Certificates.TWDK

end
