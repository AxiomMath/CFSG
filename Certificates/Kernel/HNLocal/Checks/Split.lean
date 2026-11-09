module

public import Certificates.Data.Kernel.HNLocalK
public import Certificates.Data.Kernel.HNLocalZ
public import Certificates.Data.Kernel.HNMultK
public import CFSG.Certificates.Kernel.J4Hub.BlockSound
public import CFSG.Certificates.Kernel.HNLocalSound

public section

namespace CFSG.KD.HNLocal

open CFSG.KC.HNLocal CFSG.KC.HNMult

theorem treeSum_add (XC TD MSF : Nat → Nat) (N M L H CM3 RM GA GB GFC lo a : Nat) : ∀ b,
    treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo (a + b) =
      treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo a +
        treeSum XC TD MSF N M L H CM3 RM GA GB GFC (lo + a) b
  | 0 => rfl
  | b + 1 => by
    show CFSG.KC.Loop.strictN (treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo (a + b))
        (fun s => Nat.add s (treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC (Nat.add lo (a + b)))) =
      treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo a +
        CFSG.KC.Loop.strictN (treeSum XC TD MSF N M L H CM3 RM GA GB GFC (lo + a) b)
          (fun s => Nat.add s (treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC (Nat.add (lo + a) b)))
    rw [CFSG.KS.J4Hub.strictN_eq', CFSG.KS.J4Hub.strictN_eq', treeSum_add XC TD MSF N M L H CM3 RM
      GA GB GFC lo a b]
    have e : Nat.add lo (a + b) = Nat.add (lo + a) b := by
      show lo + (a + b) = lo + a + b
      omega
    rw [e]
    exact Nat.add_assoc _ _ _

theorem treeSum_eq_add {XC TD MSF : Nat → Nat} {N M L H CM3 RM GA GB GFC lo a b va vb : Nat}
    (h1 : treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo a = va)
    (h2 : treeSum XC TD MSF N M L H CM3 RM GA GB GFC (lo + a) b = vb) :
    treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo (a + b) = va + vb := by
  rw [treeSum_add, h1, h2]

theorem treeSum_eq_add' {XC TD MSF : Nat → Nat} {N M L H CM3 RM GA GB GFC lo a b c n va vb : Nat}
    (h1 : treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo a = va)
    (h2 : treeSum XC TD MSF N M L H CM3 RM GA GB GFC c b = vb) (hc : lo + a = c) (hn : a + b = n) :
    treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo n = va + vb := by
  subst hc hn
  exact treeSum_eq_add h1 h2

theorem relWRange_add (RB : Nat → Nat) (mul : Nat → Nat → Nat) (L ONE : Nat)
    (RW : Nat → List Nat) (lo a : Nat) : ∀ b, relWRange RB mul L ONE RW lo (a + b) =
      CFSG.KC.Ord.andB (relWRange RB mul L ONE RW lo a) (relWRange RB mul L ONE RW (lo + a) b)
  | 0 => by
    show relWRange RB mul L ONE RW lo a = CFSG.KC.Ord.andB (relWRange RB mul L ONE RW lo a) true
    cases relWRange RB mul L ONE RW lo a <;> rfl
  | b + 1 => by
    show CFSG.KC.Ord.andB (relWRange RB mul L ONE RW lo (a + b))
        (relW RB mul L ONE (RW (Nat.add lo (a + b)))) =
      CFSG.KC.Ord.andB (relWRange RB mul L ONE RW lo a)
        (CFSG.KC.Ord.andB (relWRange RB mul L ONE RW (lo + a) b)
          (relW RB mul L ONE (RW (Nat.add (lo + a) b))))
    rw [relWRange_add RB mul L ONE RW lo a b]
    have e : Nat.add lo (a + b) = Nat.add (lo + a) b := by
      show lo + (a + b) = lo + a + b
      omega
    rw [e]
    cases relWRange RB mul L ONE RW lo a <;> cases relWRange RB mul L ONE RW (lo + a) b <;> rfl

theorem relWRange_of {RB : Nat → Nat} {mul : Nat → Nat → Nat} {L ONE : Nat}
    {RW : Nat → List Nat} {lo a b : Nat} (h1 : relWRange RB mul L ONE RW lo a = true)
    (h2 : relWRange RB mul L ONE RW (lo + a) b = true) :
    relWRange RB mul L ONE RW lo (a + b) = true := by
  rw [relWRange_add, h1, h2]
  rfl

theorem letB_eq' (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem cen_of {mul vm : Nat → Nat → Nat} {PC RP TG : Nat → Nat} {np ONE RM n k M idx : Nat}
    (h1 : cen mul vm PC RP TG np ONE RM n (k + 1) M idx = true)
    (h2 : cen mul vm PC RP TG np ONE RM n (k + 1) (mul M (PC k)) (idx + 1 <<< k) = true) :
    cen mul vm PC RP TG np ONE RM (n + 1) k M idx = true := by
  show Bool.rec (motive := fun _ => Bool) false
      (letB (mul M (PC k)) (fun M' => cen mul vm PC RP TG np ONE RM n (Nat.succ k) M'
        (Nat.add idx (Nat.shiftLeft (nat_lit 1) k))))
      (cen mul vm PC RP TG np ONE RM n (Nat.succ k) M idx) = true
  rw [letB_eq', show cen mul vm PC RP TG np ONE RM n (Nat.succ k) M idx = true from h1]
  exact h2

theorem zcen_of {mul vm : Nat → Nat → Nat} {PC TG : Nat → Nat} {RM Z EV n k M idx : Nat}
    (h1 : zcen mul vm PC TG RM Z EV n (k + 1) M idx = true)
    (h2 : zcen mul vm PC TG RM Z EV n (k + 1) (mul M (PC k)) (idx + 1 <<< k) = true) :
    zcen mul vm PC TG RM Z EV (n + 1) k M idx = true := by
  show Bool.rec (motive := fun _ => Bool) false
      (letB (mul M (PC k)) (fun M' => zcen mul vm PC TG RM Z EV n (Nat.succ k) M'
        (Nat.add idx (Nat.shiftLeft (nat_lit 1) k))))
      (zcen mul vm PC TG RM Z EV n (Nat.succ k) M idx) = true
  rw [letB_eq', show zcen mul vm PC TG RM Z EV n (Nat.succ k) M idx = true from h1]
  exact h2

theorem allBelow_of {m : Nat} {f : Nat → Bool} (h : ∀ i < m, f i = true) :
    ∀ hi, CFSG.KC.Loop.allBelow m hi f = true
  | 0 => rfl
  | j + 1 => by
    have inner : ∀ c, Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft j 6) l), ih2)) c =
          true := by
      intro c
      induction c with
      | zero => rfl
      | succ l ihl =>
        show bAnd(bIf(Nat.blt (Nat.add (Nat.shiftLeft j 6) l) m, f (Nat.add (Nat.shiftLeft j 6) l),
          true), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
            bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft j 6) l), ih2)) l) =
          true
        rw [ihl]
        cases hb : Nat.blt (Nat.add (Nat.shiftLeft j 6) l) m with
        | false => rfl
        | true =>
          have hf := h _ (Nat.le_of_ble_eq_true hb)
          show Bool.rec (motive := fun _ => Bool) false true (f (Nat.add (Nat.shiftLeft j 6) l)) = true
          rw [hf]
    show bAnd(Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft j 6) l), ih2)) 64,
      CFSG.KC.Loop.allBelow m j f) = true
    rw [inner 64, allBelow_of h j]

theorem sortRange_of {XC SD : Nat → Nat} {N M lo n : Nat}
    (h : ∀ i < n, sortLeaf XC SD N M (lo + i) = true) : sortRange XC SD N M lo n = true :=
  allBelow_of h _

theorem sortRange_join {XC SD : Nat → Nat} {N M lo a b : Nat}
    (h1 : sortRange XC SD N M lo a = true) (h2 : sortRange XC SD N M (lo + a) b = true) :
    sortRange XC SD N M lo (a + b) = true :=
  sortRange_of fun i hi => by
    rcases Nat.lt_or_ge i a with h | h
    · exact CFSG.KS.HNLocal.sortRange_spec h1 i h
    · have h3 := CFSG.KS.HNLocal.sortRange_spec h2 (i - a) (by omega)
      rwa [show lo + a + (i - a) = lo + i by omega] at h3

end CFSG.KD.HNLocal

end
