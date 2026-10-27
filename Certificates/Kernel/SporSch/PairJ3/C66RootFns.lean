module

public import Certificates.Kernel.SporSch.PairJ3.C66Fns

public section

namespace CertificateChecks.KernelSporSch.PJ3C66

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.PJ3C81

@[expose] def prQ (q : Nat) : Nat := [3, 5, 17, 19].getD q 0

@[expose] def pnQ (q : Nat) : Nat := [243, 5, 17, 19].getD q 0

@[expose] def oddI : List (List Nat × Nat) :=
  [([1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4, 4, 4, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 2, 4, 4, 4, 4, 4, 4, 4,
      4, 4], 5),
   ([4, 1, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 4, 1], 5),
   ([2, 0, 1, 1, 1, 1, 1, 2], 3)]

@[expose] def oddO : List (List Nat × Nat) :=
  [([2, 0, 1, 2, 1, 2, 0, 2, 0, 1, 2, 1, 2], 3), ([2, 1, 2, 1, 0, 2, 1, 0], 3)]

@[expose] def oddL (r : Nat) : List (List Nat × Nat) :=
  Bool.rec (motive := fun _ => List (List Nat × Nat)) oddO oddI (Nat.beq r 0)

@[expose] noncomputable def wP (r : Nat) (L : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun l _ ih => hP r l ih) L

@[expose] noncomputable def wI (r : Nat) (L : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y) (fun l _ ih => fun y => ih (hI r l y)) L x

@[expose] noncomputable def yW (r i : Nat) (X : Nat → Nat) (y : Nat) : Nat :=
  X (wP r ((oddL r).getD i ([], 1)).1 (X (wI r ((oddL r).getD i ([], 1)).1 y)))

@[expose] noncomputable def witT (r q t m a : Nat) (X : Nat → Nat) : Bool :=
  bIf(Nat.beq t 0, bAnd(bIf(Nat.beq (Nat.mod m (prQ q)) 0, false, true),
      eqOnL bs (powF X m) (fun x => x)),
    bAnd(Nat.blt a 6156,
    bIf(Nat.beq t 1, bIf(Nat.beq (powF X (prQ q) a) a, false, true),
      bAnd(Nat.beq t 2, bAnd(Nat.blt m (oddL r).length,
        bIf(Nat.beq (powF (yW r m X) (pnQ q) a) a, false, true))))))

@[expose] noncomputable def witOK (r q W : Nat) (X : Nat → Nat) : Bool :=
  witT r q (Nat.shiftRight W 28) (Nat.land (Nat.shiftRight W 16) 4095) (Nat.land W 65535) X

@[expose] noncomputable def rootI (k : Nat) : Bool :=
  bAnd(Nat.blt (C66D.RI k) 26163, allN 4 (fun q =>
    witOK 0 q (C66D.WI (Nat.add (Nat.mul 4 k) q)) (fun y => cP 9 (sI (C66D.RI k) y))))

@[expose] noncomputable def rootO (k : Nat) : Bool :=
  bAnd(Nat.blt (C66D.RO k) 20520, allN 4 (fun q =>
    witOK 1 q (C66D.WO (Nat.add (Nat.mul 4 k) q)) (fun y => cP 21 (sO (C66D.RO k) y))))

@[expose] noncomputable def oddEl (r : Nat) (e : List Nat × Nat) : Bool :=
  bAnd(Nat.beq (Nat.mod e.2 2) 1, eqOnL bs (powF (wP r e.1) e.2) (fun x => x))

@[expose] noncomputable def oddAllB (r : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(oddEl r e, ih)) (oddL r)

@[expose] noncomputable def rootsB : Bool :=
  bAnd(allN 27 rootI, bAnd(allN 22 rootO, bAnd(oddAllB 0, oddAllB 1)))

end CertificateChecks.KernelSporSch.PJ3C66

end
