module

public import Certificates.Kernel.RouteP.Bridge.Defs
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal
public import CFSG.Sporadic.Presentation.Common
public import Mathlib

public section

#kc_slice_range CFSG.KD.RouteP.nkP CFSG.KD.RouteP.BridgeCk.n 0 42
#kc_slice_range CFSG.KD.RouteP.zck CFSG.KD.RouteP.BridgeCk.z 0 20

namespace CFSG.KD.RouteP.BridgeCk

open CFSG.KD.RouteP CFSG.KC.RouteP CFSG.KC CFSG.KC.LceS

theorem closeS_succR (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (n s : Nat) :
    closeS NW KA KB gens (n + 1) s = closeS NW KA KB gens n (roundS NW KA KB gens s) := by
  show CFSG.KC.Loop.strictN (roundS NW KA KB gens s) (closeS NW KA KB gens n) = _
  generalize roundS NW KA KB gens s = y
  cases y <;> rfl

theorem closeS_addR (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) :
    ∀ (a b s : Nat), closeS NW KA KB gens (a + b) s = closeS NW KA KB gens b (closeS NW KA KB gens a s)
  | 0, b, s => by rw [Nat.zero_add]; rfl
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega, closeS_succR, closeS_succR, closeS_addR NW KA KB gens a b]

#kc_natval TS1 := closeS NWP KAP KBP [-1, -2] 21 (single 0)

theorem ts1 : closeS NWP KAP KBP [-1, -2] 21 (single 0) = TS1 := Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval TS2 := closeS NWP KAP KBP [-1, -2] 21 TS1

theorem ts2 : closeS NWP KAP KBP [-1, -2] 21 TS1 = TS2 := Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval TS3 := closeS NWP KAP KBP [-1, -2] 20 TS2

theorem ts3 : closeS NWP KAP KBP [-1, -2] 20 TS2 = TS3 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem tsC : closedS NWP KAP KBP [-1, -2] TS3 = true := by quickRfl

theorem letB_eqR (v : Nat) (k : Nat → Bool) : letB v k = k v := by cases v <;> rfl

@[expose] noncomputable def blkOneR (m : Nat) (f : Nat → Nat) (h : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
    Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64

@[expose] noncomputable def blkSR (m : Nat) (f : Nat → Nat) (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j ih => Nat.add (blkOneR m f (a + j)) ih) b

theorem sumBelow_addR (m : Nat) (f : Nat → Nat) (a : Nat) :
    ∀ b, CFSG.KC.Loop.sumBelow m (a + b) f = Nat.add (blkSR m f a b) (CFSG.KC.Loop.sumBelow m a f)
  | 0 => (Nat.zero_add _).symm
  | b + 1 => by
    show Nat.add (blkOneR m f (a + b)) (CFSG.KC.Loop.sumBelow m (a + b) f) =
      Nat.add (Nat.add (blkOneR m f (a + b)) (blkSR m f a b)) (CFSG.KC.Loop.sumBelow m a f)
    rw [sumBelow_addR m f a b]
    exact (Nat.add_assoc _ _ _).symm

theorem sumBelow_splitR (m : Nat) (f : Nat → Nat) (a b n : Nat) (h : a + b = n) :
    CFSG.KC.Loop.sumBelow m n f = Nat.add (blkSR m f a b) (CFSG.KC.Loop.sumBelow m a f) := by
  rw [← h]
  exact sumBelow_addR m f a b

#kc_natval PCA := CFSG.KC.Loop.sumBelow (nat_lit 24576) 128
    (fun c => pc64 (Nat.land (Nat.shiftRight (Nat.land TS3 ptsS) (Nat.mul c (nat_lit 64)))
      (nat_lit 18446744073709551615)))

theorem pcA : CFSG.KC.Loop.sumBelow (nat_lit 24576) 128
    (fun c => pc64 (Nat.land (Nat.shiftRight (Nat.land TS3 ptsS) (Nat.mul c (nat_lit 64)))
      (nat_lit 18446744073709551615))) = PCA := Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval PCB := blkSR (nat_lit 24576)
    (fun c => pc64 (Nat.land (Nat.shiftRight (Nat.land TS3 ptsS) (Nat.mul c (nat_lit 64)))
      (nat_lit 18446744073709551615))) 128 256

theorem pcB : blkSR (nat_lit 24576)
    (fun c => pc64 (Nat.land (Nat.shiftRight (Nat.land TS3 ptsS) (Nat.mul c (nat_lit 64)))
      (nat_lit 18446744073709551615))) 128 256 = PCB := Nat.eq_of_beq_eq_true (by quickRfl)

theorem orbOK_of_segs (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (x T1 T2 T3 PA PB : Nat)
    (h1 : closeS NW KA KB gens 21 (single x) = T1) (h2 : closeS NW KA KB gens 21 T1 = T2)
    (h3 : closeS NW KA KB gens 20 T2 = T3) (hc : closedS NW KA KB gens T3 = true)
    (hA : CFSG.KC.Loop.sumBelow (nat_lit 24576) 128
      (fun c => pc64 (Nat.land (Nat.shiftRight (Nat.land T3 ptsS) (Nat.mul c (nat_lit 64)))
        (nat_lit 18446744073709551615))) = PA)
    (hB : blkSR (nat_lit 24576)
      (fun c => pc64 (Nat.land (Nat.shiftRight (Nat.land T3 ptsS) (Nat.mul c (nat_lit 64)))
        (nat_lit 18446744073709551615))) 128 256 = PB)
    (hs : Nat.beq (Nat.add PB PA) 920808 = true) :
    orbOK NW KA KB gens x 62 920808 = true := by
  unfold orbOK
  rw [show (62 : Nat) = 21 + (21 + 20) from rfl, closeS_addR, h1, closeS_addR, h2, h3, letB_eqR, hc]
  unfold pcount
  rw [sumBelow_splitR (nat_lit 24576) _ 128 256 (nat_lit 384) rfl, hA, hB, hs]
  rfl

theorem trans : CFSG.KD.RouteP.transOK = true :=
  orbOK_of_segs NWP KAP KBP [-1, -2] 0 TS1 TS2 TS3 PCA PCB ts1 ts2 ts3 tsC pcA pcB rfl

theorem zp : CFSG.KD.RouteP.zpOK = true := by quickRfl

end CFSG.KD.RouteP.BridgeCk

end
