module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Data.Kernel.SporCov.BaseKit
public import Certificates.Data.Kernel.SporCov.Census

#kc_repo #kc_json_gz CFSG.KD.SporCovPerm.M11.F "Certificates/Kernel/SporCovPerm/data/m11.json.gz" 6910
  3807064662332269088
  (A : List (List Nat)) (S1 : List Nat) (S2 : List Nat) (SC : List (List Nat)) (J1 : Nat)
  (SM : List Nat) (NW : List (List Nat)) (NS : List Nat) (NC : List Nat) (H : List (List Nat))
  (HI : List (List Nat)) (PW : List (List Nat)) (PI : List Nat) (N1 : List Nat) (N1i : List Nat)
  (N2 : List Nat) (N2i : List Nat) (WA : List (List Nat)) (WB : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovPerm.M11

open CFSG.KC.SporCov

@[expose] noncomputable def bs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

@[expose] noncomputable def fA : Nat → Nat := nthN (nthW F.A 0)
@[expose] noncomputable def fAi : Nat → Nat := nthN (nthW F.A 1)
@[expose] noncomputable def fB : Nat → Nat := nthN (nthW F.A 2)
@[expose] noncomputable def fBi : Nat → Nat := nthN (nthW F.A 3)

@[expose] noncomputable def E : List Nat → List Nat → Bool := eqB fA fAi fB fBi bs

@[expose] noncomputable def im (w : List Nat) (x : Nat) : Nat := imB fA fAi fB fBi w x

@[expose] noncomputable def keyL (f : Nat → Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add (f x) (Nat.mul 16 ih)) l

@[expose] noncomputable def key (w : List Nat) : Nat := keyL (im w) bs

@[expose] noncomputable def pf (w : List Nat) : Bool := Nat.blt (im w 0) 2 && Nat.blt (im w 1) 2

@[expose] noncomputable def sW (k : Nat) : List Nat := cond (Nat.beq k 0) F.S1 F.S2

@[expose] noncomputable def sT (i : Nat) : List Nat := expC [F.S1, F.S2] (nthW F.SC i)

@[expose] noncomputable def nW (t : Nat) : List Nat := nthW F.NW t

@[expose] noncomputable def gM (i : Nat) : List (List Nat) :=
  [F.N1, F.N1i, F.N2, F.N2i, nthW F.H i, nthW F.HI i]

@[expose] noncomputable def chS0 : Bool :=
  Nat.beq (im F.S1 0) 0 && Nat.beq (im F.S1 1) 1 && Nat.beq (im F.S2 0) 0 && Nat.beq (im F.S2 1) 1 &&
    allLt 11 fun x => Nat.blt x 2 || !Nat.beq (im F.S1 x) x || !Nat.beq (im F.S2 x) x

@[expose] noncomputable def chS : Bool :=
  Nat.blt F.J1 9 && E (sT F.J1) [] &&
    (allLt 8 fun i => Nat.blt (key (sT i)) (key (sT (i + 1)))) &&
    allLt 9 fun i => allLt 2 fun k =>
      Nat.blt (nthN F.SM (4 * i + 2 * k)) 9 && E (sW k ++ sT i) (sT (nthN F.SM (4 * i + 2 * k))) &&
        Nat.blt (nthN F.SM (4 * i + 2 * k + 1)) 9 &&
          E (sT i) (sW k ++ sT (nthN F.SM (4 * i + 2 * k + 1)))

@[expose] noncomputable def chN : Bool :=
  (allLt 143 fun t => Nat.blt (key (nW t)) (key (nW (t + 1)))) && allLt 144 fun t => pf (nW t)

@[expose] noncomputable def chNS : Bool :=
  allLt 144 fun t => allLt 2 fun k =>
    Nat.blt (nthN F.NS (2 * t + k)) 9 && E (sW k ++ nW t) (nW t ++ sT (nthN F.NS (2 * t + k)))

@[expose] noncomputable def chNC : Bool :=
  allLt 144 fun t =>
    cond (Nat.blt (nthN F.NC t) 9) (E (nW t) (sT (nthN F.NC t)))
      (!E (sW (nthN F.NC t - 9) ++ nW t) (nW t ++ sW (nthN F.NC t - 9)))

@[expose] noncomputable def pairOK (x y : Nat) (w : List Nat) (i : Nat) : Bool :=
  pf w && Nat.blt i 2 &&
    ((Nat.beq (im w x) (im (nthW F.H i) 0) && Nat.beq (im w y) (im (nthW F.H i) 1)) ||
      (Nat.beq (im w x) (im (nthW F.H i) 1) && Nat.beq (im w y) (im (nthW F.H i) 0)))

@[expose] noncomputable def chP : Bool :=
  allLt 11 fun x => allLt 11 fun y =>
    !Nat.blt x y || (Nat.beq x 0 && Nat.beq y 1) ||
      pairOK x y (nthW F.PW (11 * x + y)) (nthN F.PI (11 * x + y))

@[expose] noncomputable def chG : Bool :=
  pf F.N1 && pf F.N2 && E (F.N1 ++ F.N1i) [] && E (F.N2 ++ F.N2i) [] &&
    allLt 2 fun i => E (nthW F.H i ++ nthW F.HI i) [] && E (expC (gM i) (nthW F.WA i)) [0] &&
      E (expC (gM i) (nthW F.WB i)) [2]

@[expose] noncomputable def chk : Bool := chS0 && chS && chN && chNS && chNC && chP && chG

namespace Ck

theorem ok : chk = true := by quickRfl

end Ck

end CFSG.KD.SporCovPerm.M11

end
