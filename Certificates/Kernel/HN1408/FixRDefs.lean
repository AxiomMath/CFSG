module

public import Certificates.Kernel.HN1408.M11Defs
public import Certificates.Kernel.HN1408.FixRData3
public import Certificates.Kernel.HN1408.FixRData5a
public import Certificates.Kernel.HN1408.FixRData5b
public import Certificates.Kernel.HN1408.FixRData5c
public import Certificates.Kernel.HN1408.FixRData7

public section

namespace CFSG.KD.HN1408.FixR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def gHeadF (ws : List (List Nat)) (G GI : Nat → Nat) : Bool :=
  allN ws.length fun j => bAnd(Nat.beq (G j) (WK (ws.getD j [])),
    Nat.beq (GI j) (WK (ws.getD j []).reverse))

@[expose] noncomputable def yGenF (yws : List (List Nat)) (YG : Nat → Nat) : Bool :=
  allN yws.length fun l => Nat.beq (YG l) (WK (yws.getD l []))

@[expose] noncomputable def yTreeF (YG Y YI YP : Nat → Nat) (nYG nY : Nat) : Bool :=
  bAnd(Nat.beq (Y 0) idK, allN nY fun k => strictB (Y k) fun A =>
    bAnd(Nat.beq (pt A 0) 0, bAnd(Nat.beq (pc (YI k) A) idK,
      bIf(Nat.beq k 0, true, strictB (YP k) fun w => strictB (f16 w 0) fun p =>
        strictB (f16 w 1) fun l =>
          bAnd(Nat.blt p k, bAnd(Nat.blt l nYG, Nat.beq A (pc (YG l) (Y p))))))))

@[expose] noncomputable def fixCntF (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc (nIf(Nat.beq (pt X i) i, 1, 0))) 1408

@[expose] noncomputable def cyF (Y YI : Nat → Nat) (k X : Nat) : Nat := pc (pc (Y k) X) (YI k)

@[expose] noncomputable def keyF (Y YI : Nat → Nat) (X k : Nat) : Nat :=
  strictN (Y k) fun A => strictN (YI k) fun B =>
    Nat.add (pt A (pt X (pt B 1)))
      (Nat.add (Nat.mul 2048 (pt A (pt X (pt B 2))))
        (Nat.add (Nat.mul 4194304 (pt A (pt X (pt B 3))))
          (Nat.mul 8589934592 (pt A (pt X (pt B 4))))))

@[expose] noncomputable def repF (G GI Y YI R P : Nat → Nat) (nG nY i : Nat) : Bool :=
  strictB (P i) fun q => strictB (f16 q 0) fun p => strictB (f16 q 1) fun k =>
    strictB (f16 q 2) fun j =>
      bAnd(Nat.blt p i, bAnd(Nat.blt k nY, bAnd(Nat.blt j nG, bAnd(Nat.beq (pt (R i) 0) 0,
        bIf(Nat.beq k 0, Nat.beq (R i) (pc (pc (G j) (R p)) (GI j)),
          Nat.beq (R i) (pc (pc (G j) (cyF Y YI k (R p))) (GI j)))))))

@[expose] noncomputable def repFSl (G GI Y YI R P : Nat → Nat) (nG nY n a len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add a d) fun i =>
    bIf(Nat.blt i n, bIf(Nat.beq i 0, true, repF G GI Y YI R P nG nY i), true)

@[expose] noncomputable def sortFAt (Y YI R S : Nat → Nat) (nY n cnt m : Nat) : Bool :=
  strictB (S m) fun s => bAnd(Nat.blt (f16 s 0) n, bAnd(Nat.blt (f16 s 1) nY,
    bIf(Nat.blt (m + 1) cnt, strictB (S (m + 1)) fun s' =>
      Nat.blt (keyF Y YI (R (f16 s 0)) (f16 s 1)) (keyF Y YI (R (f16 s' 0)) (f16 s' 1)), true)))

@[expose] noncomputable def sortFSl (Y YI R S : Nat → Nat) (nY n cnt a len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add a d) fun m => bIf(Nat.blt m cnt, sortFAt Y YI R S nY n cnt m, true)

@[expose] noncomputable def headF (ws yws : List (List Nat)) (w : List Nat) (fix nY : Nat)
    (G GI YG Y YI YP R : Nat → Nat) : Bool :=
  bAnd(gHeadF ws G GI, bAnd(yGenF yws YG, bAnd(yTreeF YG Y YI YP yws.length nY,
    bAnd(Nat.beq (R 0) (WK w), Nat.beq (fixCntF (R 0)) fix))))

@[expose] def cw0 : List (List Nat) := p0Words

@[expose] def cw5b : List (List Nat) := p0Words ++ [fix5B.conjs.getD 1 []]

@[expose] def cw7 : List (List Nat) := p0Words ++ [fix7.conjs.getD 1 []]

@[expose] def yw7 : List (List Nat) := [p0Words.getD 1 []]

@[expose] def yw3 : List (List Nat) :=
  [p0Words.getD 1 [] ++ p0Words.getD 0 [] ++ p0Words.getD 0 [] ++ p0Words.getD 0 []]

@[expose] noncomputable def f3Head : Bool :=
  headF cw0 yw7 fix3.rep fix3.fix 7 Fix3.G Fix3.GI Fix3.YG Fix3.Y Fix3.YI Fix3.YP Fix3.R
@[expose] noncomputable def f3Rep (s : Nat) : Bool :=
  repFSl Fix3.G Fix3.GI Fix3.Y Fix3.YI Fix3.R Fix3.P 2 7 500 (Nat.mul 100 s) 100
@[expose] noncomputable def f3Sort (s : Nat) : Bool :=
  sortFSl Fix3.Y Fix3.YI Fix3.R Fix3.S 7 500 3500 (Nat.mul 2200 s) 2200

@[expose] noncomputable def f5aHead : Bool :=
  headF cw0 yw3 fix5A.rep fix5A.fix 3 Fix5a.G Fix5a.GI Fix5a.YG Fix5a.Y Fix5a.YI Fix5a.YP Fix5a.R
@[expose] noncomputable def f5aRep (s : Nat) : Bool :=
  repFSl Fix5a.G Fix5a.GI Fix5a.Y Fix5a.YI Fix5a.R Fix5a.P 2 3 168 (Nat.mul 100 s) 100
@[expose] noncomputable def f5aSort (s : Nat) : Bool :=
  sortFSl Fix5a.Y Fix5a.YI Fix5a.R Fix5a.S 3 168 504 (Nat.mul 2200 s) 2200

@[expose] noncomputable def f5bHead : Bool :=
  headF cw5b yw3 fix5B.rep fix5B.fix 3 Fix5b.G Fix5b.GI Fix5b.YG Fix5b.Y Fix5b.YI Fix5b.YP Fix5b.R
@[expose] noncomputable def f5bRep (s : Nat) : Bool :=
  repFSl Fix5b.G Fix5b.GI Fix5b.Y Fix5b.YI Fix5b.R Fix5b.P 3 3 3360 (Nat.mul 100 s) 100
@[expose] noncomputable def f5bSort (s : Nat) : Bool :=
  sortFSl Fix5b.Y Fix5b.YI Fix5b.R Fix5b.S 3 3360 10080 (Nat.mul 2200 s) 2200

@[expose] noncomputable def f5cHead : Bool :=
  headF cw0 yw7 fix5C.rep fix5C.fix 7 Fix5c.G Fix5c.GI Fix5c.YG Fix5c.Y Fix5c.YI Fix5c.YP Fix5c.R
@[expose] noncomputable def f5cRep (s : Nat) : Bool :=
  repFSl Fix5c.G Fix5c.GI Fix5c.Y Fix5c.YI Fix5c.R Fix5c.P 2 7 720 (Nat.mul 100 s) 100
@[expose] noncomputable def f5cSort (s : Nat) : Bool :=
  sortFSl Fix5c.Y Fix5c.YI Fix5c.R Fix5c.S 7 720 5040 (Nat.mul 2200 s) 2200

@[expose] noncomputable def f7Head : Bool :=
  headF cw7 sylow5Words fix7.rep fix7.fix 125 Fix7.G Fix7.GI Fix7.YG Fix7.Y Fix7.YI Fix7.YP Fix7.R
@[expose] noncomputable def f7Rep (s : Nat) : Bool :=
  repFSl Fix7.G Fix7.GI Fix7.Y Fix7.YI Fix7.R Fix7.P 3 125 288 (Nat.mul 100 s) 100
@[expose] noncomputable def f7Sort (s : Nat) : Bool :=
  sortFSl Fix7.Y Fix7.YI Fix7.R Fix7.S 125 288 36000 (Nat.mul 2200 s) 2200

end CFSG.KD.HN1408.FixR

end
