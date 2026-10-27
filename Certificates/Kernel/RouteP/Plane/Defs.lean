module

public import Certificates.Kernel.RouteP.Plane.Data
public import Certificates.Kernel.RouteP.Text.Data

public section

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP

@[expose] def pReg (k : Nat) : Nat :=
  if k < 2 then 53 + 4 * k else if k < 13 then 31 + 2 * (k - 2) else k - 7

@[expose] def pl (l : Int) : Int :=
  if 0 < l then -((pReg (l.toNat - 1) : Int) + 1) else (pReg ((-l).toNat - 1) : Int) + 1

@[expose] def dW0 : List Int :=
  [-2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2]

@[expose] def dW1 : List Int :=
  [-1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2]

@[expose] def uW : List Int := [14, -15, -15, 16, 14]

@[expose] def vW : List Int := [-16, -14, 15, 16, 15, 16]

@[expose] def invPW (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def wT (e : Nat) : List Int :=
  if e = 0 then dW0 else if e = 1 then dW1 else invPW uW ++ invPW vW ++ uW ++ vW

@[expose] def wP (e : Nat) : List Int := (wT e).map pl

@[expose] def zl (s : Nat) : Int :=
  if s < 2 then ((59 + s : Nat) : Int) else if s < 13 then pl ((s : Int) + 1) else 61

@[expose] noncomputable def pS (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j _ ih => Nat.lor (single (PXE i j)) ih) (List.range 24)

@[expose] noncomputable def pnk (e : Nat) : Bool :=
  andB (CFSG.KC.Fi24Net.netOK (NWQ (Nat.add (nat_lit 58) e))) (kapOK KAQ KBQ (Nat.add (nat_lit 58) e))

@[expose] noncomputable def pwck (g : Nat) : Bool :=
  (fun e k => Bool.rec (motive := fun _ => Bool)
      (wordKOK NWQ KAQ KBQ (wP e) (Nat.add (nat_lit 58) e))
      (CFSG.KC.RouteP.wordOK NWQ (wP e) (Nat.add (nat_lit 58) e) k) (Nat.blt k (nat_lit 19)))
    (Nat.div g (nat_lit 20)) (Nat.mod g (nat_lit 20))

@[expose] def fixPt (p : Nat) : Nat := if p = 0 then 0 else if p = 1 then 1479 else 99705

@[expose] def fW (t : Nat) : List Int :=
  if t < 14 then [zl t] else if t = 14 then uW.map pl else vW.map pl

@[expose] noncomputable def pfck (g : Nat) : Bool :=
  (fun x => ptOK NWQ KAQ KBQ (fW (Nat.div g (nat_lit 3))) x x) (fixPt (Nat.mod g (nat_lit 3)))

@[expose] noncomputable def pack (g : Nat) : Bool :=
  (fun s i => Nat.beq (imgS NWQ KAQ KBQ (zl s) (pS i)) (pS (PGE s i)))
    (Nat.div g (nat_lit 891)) (Nat.mod g (nat_lit 891))

end CFSG.KD.RouteP

end
