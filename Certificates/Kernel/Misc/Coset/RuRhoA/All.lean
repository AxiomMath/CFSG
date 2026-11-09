module

public import Certificates.Kernel.Misc.Coset.RuRhoA.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.RuRho

open CFSG.KC.MiscCoset.Act

@[expose] noncomputable def relsTriv (A B : Nat → Nat) (m N T x : Nat) (R : List (List Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih k => andB
      (Bool.rec
        (andB (Nat.beq (walk A (Nat.add m m) r x) (B (Nat.add (Nat.mul k N) x)))
          (allR 0 m fun g => Nat.beq
            (B (Nat.add (Nat.mul k N) (step A (Nat.add m m) x (Nat.add g g))))
            (step A (Nat.add m m) (B (Nat.add (Nat.mul k N) x)) (Nat.add g g))))
        (andB (Nat.beq (walk A (Nat.add m m) r x) x) (Nat.beq (B (Nat.add (Nat.mul k N) x)) x))
        (Nat.beq (Nat.land (Nat.shiftRight T k) 1) 1))
      (ih (Nat.succ k))) R

@[expose] noncomputable def coverPointOKT (A B : Nat → Nat) (m N T : Nat)
    (R W : List (List Nat)) (x : Nat) : Bool :=
  andB (allR 0 (Nat.add m m) fun c => Nat.blt (step A (Nat.add m m) x c) N)
  (andB (allR 0 m fun g =>
    andB (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.add g g))
      (Nat.succ (Nat.add g g))) x)
    (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.succ (Nat.add g g)))
      (Nat.add g g)) x))
  (andB (relsTriv A B m N T x R 0) (relsAt A (Nat.add m m) W x)))

theorem allR_of_forall {lo n : ℕ} {p : ℕ → Bool}
    (h : ∀ x, lo ≤ x → x < lo + n → p x = true) : allR lo n p = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allR_succ, Bool.and_eq_true]
    exact ⟨h _ (Nat.le_add_right _ _) (by omega), ih fun x h1 h2 => h x h1 (by omega)⟩

theorem relsTriv_cover {A B : Nat → Nat} {m N T x : Nat}
    (hx : x < N) (hb : ∀ g < m, step A (Nat.add m m) x (Nat.add g g) < N) :
    ∀ (R : List (List Nat)) (k : Nat), (∀ y < N, relsTriv A B m N T y R k = true) →
      List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun r _ ih k => andB
          (Nat.beq (walk A (Nat.add m m) r x) (B (Nat.add (Nat.mul k N) x)))
          (andB (allR 0 m fun g => Nat.beq
            (B (Nat.add (Nat.mul k N) (step A (Nat.add m m) x (Nat.add g g))))
            (step A (Nat.add m m) (B (Nat.add (Nat.mul k N) x)) (Nat.add g g)))
          (ih (Nat.succ k)))) R k = true := by
  intro R
  induction R with
  | nil => intro _ _; rfl
  | cons r R ih =>
    intro k H
    have hd : ∀ y < N, (Bool.rec
        (andB (Nat.beq (walk A (Nat.add m m) r y) (B (Nat.add (Nat.mul k N) y)))
          (allR 0 m fun g => Nat.beq
            (B (Nat.add (Nat.mul k N) (step A (Nat.add m m) y (Nat.add g g))))
            (step A (Nat.add m m) (B (Nat.add (Nat.mul k N) y)) (Nat.add g g))))
        (andB (Nat.beq (walk A (Nat.add m m) r y) y) (Nat.beq (B (Nat.add (Nat.mul k N) y)) y))
        (Nat.beq (Nat.land (Nat.shiftRight T k) 1) 1) : Bool) = true ∧
        relsTriv A B m N T y R (Nat.succ k) = true := by
      intro y hy
      have := H y hy
      change andB _ _ = true at this
      rw [andB_eq, Bool.and_eq_true] at this
      exact this
    change andB _ (andB _ _) = true
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true]
    have htail := ih (Nat.succ k) (fun y hy => (hd y hy).2)
    cases hf : Nat.beq (Nat.land (Nat.shiftRight T k) 1) 1
    · have h1 := (hd x hx).1
      rw [hf] at h1
      change andB _ _ = true at h1
      rw [andB_eq, Bool.and_eq_true] at h1
      exact ⟨h1.1, h1.2, htail⟩
    · have hid : ∀ y < N, walk A (Nat.add m m) r y = y ∧ B (Nat.add (Nat.mul k N) y) = y := by
        intro y hy
        have h1 := (hd y hy).1
        rw [hf] at h1
        change andB _ _ = true at h1
        rw [andB_eq, Bool.and_eq_true] at h1
        exact ⟨Nat.eq_of_beq_eq_true h1.1, Nat.eq_of_beq_eq_true h1.2⟩
      refine ⟨?_, ?_, htail⟩
      · rw [(hid x hx).1, (hid x hx).2]
        exact Nat.beq_refl x
      · refine allR_of_forall fun g _ hg => ?_
        rw [(hid _ (hb g (by omega))).2, (hid x hx).2]
        exact Nat.beq_refl _

theorem coverPointOK_of_T {A B : Nat → Nat} {m N T : Nat} {R W : List (List Nat)}
    (h : allR 0 N (coverPointOKT A B m N T R W) = true) :
    allR 0 N (coverPointOK A B m N R W) = true := by
  have h' : ∀ x < N, coverPointOKT A B m N T R W x = true :=
    fun x hx => allR_spec h x (Nat.zero_le x) (by omega)
  refine allR_of_forall fun x _ hx => ?_
  have hx : x < N := by omega
  have h0 := h' x hx
  unfold coverPointOKT at h0
  rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h0
  unfold coverPointOK
  rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨h0.1, h0.2.1, ?_, h0.2.2.2⟩
  refine relsTriv_cover (T := T) hx (fun g hg => ?_) R 0 (fun y hy => ?_)
  · have := allR_spec h0.1 (Nat.add g g) (Nat.zero_le _) (by simp only [Nat.add_eq]; omega)
    exact Nat.le_of_ble_eq_true this
  · have h1 := h' y hy
    unfold coverPointOKT at h1
    rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
    exact h1.2.2.1

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 16240) (CFSG.KC.MiscCoset.Act.coverPointOK CFSG.KAct.RuRho.A CFSG.KAct.RuRho.B (nat_lit 3) (nat_lit 16240) CFSG.KAct.RuRho.R CFSG.KAct.RuRho.W) = true := by
  refine coverPointOK_of_T (T := nat_lit 3063) ?_
  allR_blocks 10

end CFSG.KAct.RuRho

end

