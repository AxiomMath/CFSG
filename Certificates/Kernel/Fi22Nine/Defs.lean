module

public import Certificates.Kernel.Sporadic.Fi22.F3151D
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.E2065T
public import Certificates.Kernel.Fi22Nine.Data

public section

namespace CertificateChecks.KernelSpor.Fi22Nine

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fi22F2 (gI bT)

@[expose] noncomputable def zP : Nat := Fi22ExtT.L 22

@[expose] noncomputable def tS (s y : Nat) : Nat := pg 12 (mask 12) (Fi22X.TS s) y

@[expose] noncomputable def commB (I s t : Nat) : Bool :=
  Nat.beq (gI I (tS s (bT t))) (tS s (gI I (bT t)))

@[expose] noncomputable def centB (I : Nat) : Bool :=
  allN 9 fun s => allN 6 fun t => commB I s t

@[expose] noncomputable def oneOrZ (Z I : Nat) : Bool :=
  bIf(allN 6 fun t => Nat.beq (gI I (bT t)) (bT t), true,
    allN 6 fun t => Nat.beq (gI I (bT t)) (pg 12 (mask 12) Z (bT t)))

@[expose] noncomputable def centKz (Z I : Nat) : Bool := bIf(centB I, oneOrZ Z I, true)

@[expose] noncomputable def centK (I : Nat) : Bool := centKz zP I

@[expose] noncomputable def centSl (q : Nat) : Bool :=
  allN 4096 fun d => centK (Nat.add (Nat.mul q 4096) d)

@[expose] noncomputable def cG (j y : Nat) : Nat := pg 12 (mask 12) (Fi22CentT.L (Nat.add 19 j)) y

@[expose] noncomputable def pG (j y : Nat) : Nat := pg 12 (mask 12) (Fi22CGT.F j) y

@[expose] noncomputable def uO (y : Nat) : Nat := pg 12 (mask 12) Fi22X.GO y

@[expose] noncomputable def zO (y : Nat) : Nat := pg 12 (mask 12) zP y

@[expose] noncomputable def wL (i k : Nat) : Nat := pg 4 (mask 4) (Fi22NineD.W i) k

@[expose] noncomputable def walk (G : Nat → Nat → Nat) (i n y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun k ih y => strictN (G (wL i k) y) ih) n y

@[expose] noncomputable def xW (y : Nat) : Nat := walk cG 0 51 y
@[expose] noncomputable def yW (y : Nat) : Nat := walk cG 1 37 y
@[expose] noncomputable def aW (y : Nat) : Nat := walk cG 2 67 y
@[expose] noncomputable def hW (y : Nat) : Nat := walk cG 3 58 y
@[expose] noncomputable def h1W (y : Nat) : Nat := walk cG 4 74 y
@[expose] noncomputable def gW (y : Nat) : Nat := walk pG 5 1805 y
@[expose] noncomputable def pW (y : Nat) : Nat := walk pG 6 353 y

@[expose] noncomputable def X0 : List Nat := [1122, 1226, 1920, 2321, 2506, 2743]

@[expose] noncomputable def X1 : List Nat :=
  [63, 244, 512, 650, 1033, 1122, 1226, 1405, 1762, 1925, 2058, 2313, 2483, 2501, 2620, 3359,
    3416, 3446]

@[expose] noncomputable def memL (l : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a y, true, ih)) l

@[expose] noncomputable def fixL (l : List Nat) (m : Nat) (f : Nat → Nat) : Bool :=
  allN m fun i => memL l (f (l.getD i 0))

@[expose] noncomputable def eqB (f f' : Nat → Nat) : Bool :=
  allN 6 fun t => Nat.beq (f (bT t)) (f' (bT t))

@[expose] noncomputable def zI : Nat := pg 17 (mask 17) (Fi22NineD.Z 0) 0

@[expose] noncomputable def elemK : Bool :=
  bAnd(eqB (fun b => xW (xW (xW b))) (fun b => b),
  bAnd(eqB (fun b => yW (yW (yW b))) (fun b => b),
  bAnd(eqB (fun b => aW (aW (aW b))) (fun b => b),
  bAnd(eqB (fun b => xW (yW b)) (fun b => yW (xW b)),
  bAnd(Bool.not (eqB xW (fun b => b)),
  bAnd(Bool.not (eqB yW (fun b => b)),
  bAnd(Bool.not (eqB yW xW),
  bAnd(Bool.not (eqB yW (fun b => xW (xW b))),
  bAnd(Bool.not (eqB aW (fun b => b)),
  bAnd(eqB (fun b => aW (gW (aW b))) gW,
  bAnd(eqB (fun b => pW (hW (zO b))) (fun b => uO (zO (uO (pW (hW b))))),
  bAnd(eqB (fun b => pW (h1W (zO b))) (fun b => uO (zO (uO (pW (h1W b))))),
  bAnd(fixL X0 6 xW, bAnd(fixL X0 6 yW, bAnd(fixL X1 18 aW,
  bAnd(fixL X0 6 (fun q => uO (pW (hW q))),
  bAnd(fixL X0 6 (fun q => uO (pW (h1W q))), bAnd(fixL X1 18 (fun q => uO (pW (h1W q))),
  bAnd(allN 9 (fun s => bAnd(fixL X0 6 (tS s), fixL X1 18 (tS s))),
  bAnd(Nat.blt zI 131072,
  bAnd(allN 3510 (fun q => Nat.beq (zO q) (gI zI q)),
  bAnd(centB zI, Bool.not (eqB zO (fun b => b))))))))))))))))))))))))

@[expose] noncomputable def oF (o f k : Nat) : Nat :=
  pg 12 (mask 12) (Fi22NineD.O (Nat.add (Nat.mul o 6) f)) k

@[expose] noncomputable def oP (o m k i : Nat) : Nat := oF o 0 (Nat.add (Nat.mul k m) i)

@[expose] noncomputable def memO (o m k y : Nat) : Bool :=
  Bool.not (allN m fun i => Bool.not (Nat.beq (oP o m k i) y))

@[expose] noncomputable def mapsO (o m j k : Nat) (f : Nat → Nat) : Bool :=
  allN m fun i => memO o m k (f (oP o m j i))

@[expose] noncomputable def keyO (o m k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (oP o m k i))) m

@[expose] noncomputable def rowO (o m n : Nat) (X : List Nat) (k : Nat) : Bool :=
  bAnd(allN (Nat.sub m 1) (fun i => Nat.blt (oP o m k i) (oP o m k (Nat.add i 1))),
  bAnd(Nat.blt (oP o m k (Nat.sub m 1)) 3510,
  bAnd(bIf(Nat.blt (Nat.add k 1) n, Nat.blt (keyO o m k) (keyO o m (Nat.add k 1)), true),
    bIf(Nat.beq k (oF o 5 0),
      bAnd(allN m (fun i => Nat.beq (oP o m k i) (X.getD i 0)),
        bAnd(Nat.beq (oF o 3 k) 0, allN 9 fun s => mapsO o m k k (tS s))),
      strictB (oF o 1 k) fun j => strictB (oF o 2 k) fun s => strictB (oF o 4 k) fun w =>
        bAnd(Nat.blt j n, bAnd(Nat.blt (oF o 3 j) (oF o 3 k), bAnd(Nat.blt s 9,
        bAnd(mapsO o m j k (cG s), bAnd(Nat.blt w 9,
          Bool.not (mapsO o m k k (tS w)))))))))))

@[expose] noncomputable def orbK : Bool :=
  bAnd(Nat.blt (oF 0 5 0) 45, bAnd(Nat.blt (oF 1 5 0) 135,
  bAnd(allN 45 (rowO 0 6 45 X0), allN 135 (rowO 1 18 135 X1))))

end CertificateChecks.KernelSpor.Fi22Nine

end
