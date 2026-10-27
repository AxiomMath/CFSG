module

public import Certificates.Kernel.HN1408.M11Data
public import Certificates.Kernel.HN1408.M11Lem

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def headM (ws : List (List Nat)) (k m : Nat) (G GI GJ T PL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(Nat.beq ws.length k, bAnd(allN k fun j => bAnd(Nat.beq (GI j) (WK (ws.getD j [])),
    bAnd(Nat.beq (G j) idK, bAnd(canonK 1408 11 (mask 11) (1408 * 11) (GJ j),
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j)))),
    bAnd(Nat.beq cnt m, penumHdK idK cnt 1000000 T PL)))


@[expose] noncomputable def peA (s : Nat) : Bool :=
  penumSlK 1408 11 (mask 11) (1408 * 11) true MR1.G MR1.GI 2 MR1.cnt MR1.T MR1.PL MR1.POS MR1.SRT
    MR1.SRI (Nat.mul 1980 s) 1980
@[expose] noncomputable def hsA (s : Nat) : Bool :=
  slK MR1.cnt (hsortPtK 1408 11 (mask 11) MR1.cnt MR1.T MR1.HS MR1.HSI) (Nat.mul 3960 s) 3960
@[expose] noncomputable def clA (s : Nat) : Bool :=
  slK (Nat.mul MR1.cnt 4) (findPtK MR1.cnt MR1.T (prodQK 1408 11 (mask 11) 4 MR1.T
    (bothK 2 MR1.GI MR1I)) MR1Cl) (Nat.mul 1980 s) 1980


@[expose] noncomputable def ordK (X e : Nat) : Bool :=
  strictB (pc X X) fun x2 => strictB (pc x2 x2) fun x4 =>
    bIf(Nat.beq e 8, Nat.beq (pc x4 x4) idK,
    bIf(Nat.beq e 6, strictB (pc X x2) fun x3 => Nat.beq (pc x3 x3) idK,
    bIf(Nat.beq e 5, Nat.beq (pc X x4) idK,
    bIf(Nat.beq e 11, Nat.beq (pc X (pc (pc x4 x4) x2)) idK, false))))

@[expose] noncomputable def oA (s : Nat) : Bool :=
  slK MR1.cnt (fun i => strictB (MR1.T i) fun x => ordK x (MO i)) (Nat.mul 990 s) 990

@[expose] noncomputable def f16 (W i : Nat) : Nat := Nat.land (Nat.shiftRight W (Nat.mul 16 i)) 65535

@[expose] noncomputable def jK (N1 N1I Y J W : Nat) : Bool :=
  strictB (f16 W 0) fun kd => strictB (f16 W 1) fun k =>
    bIf(Nat.beq kd 0, bAnd(Nat.blt k MR1.cnt, Nat.beq (MR1.T k) J),
    bIf(Nat.beq kd 1, bAnd(Nat.blt k MR1.cnt, Nat.beq (MR1.T k) (pc (pc N1 J) N1I)),
      bAnd(Nat.blt k 6, probeNeg Y J (m11Probes.getD k []) (f16 W 2) (f16 W 3) (f16 W 4)
        (f16 W 5))))

@[expose] noncomputable def jAll (cnt : Nat) (T W : Nat → Nat) : Bool :=
  strictB (WK n1Word) fun N1 => strictB (MInv 2) fun N1I => strictB (WK y0Word) fun Y =>
    allN cnt fun i => strictB (T i) fun J => jK N1 N1I Y J (W i)

@[expose] noncomputable def repK (R P : Nat → Nat) (i : Nat) : Bool :=
  strictB (P i) fun q => strictB (f16 q 0) fun p => strictB (f16 q 1) fun k =>
    strictB (f16 q 2) fun j => strictB (WK [j + 1]) fun G =>
      bAnd(Nat.blt p i, bAnd(Nat.blt k 11, bAnd(Nat.blt j 7,
        Nat.beq (R i) (pc (pc G (pc (pc (MYP k) (R p)) (MYP (11 - k)))) G))))

@[expose] noncomputable def keyK (X k : Nat) : Nat :=
  Nat.add (pt (MYP k) (pt X (pt (MYP (11 - k)) 0)))
    (Nat.add (Nat.mul 2048 (pt (MYP k) (pt X (pt (MYP (11 - k)) 1))))
      (Nat.add (Nat.mul 4194304 (pt (MYP k) (pt X (pt (MYP (11 - k)) 2))))
        (Nat.mul 8589934592 (pt (MYP k) (pt X (pt (MYP (11 - k)) 3))))))

@[expose] noncomputable def sortK (R S : Nat → Nat) (n cnt : Nat) : Bool :=
  allN cnt fun m => strictB (S m) fun s => bAnd(Nat.blt (f16 s 0) n, bAnd(Nat.blt (f16 s 1) 11,
    bIf(Nat.blt (m + 1) cnt, strictB (S (m + 1)) fun s' =>
      Nat.blt (keyK (R (f16 s 0)) (f16 s 1)) (keyK (R (f16 s' 0)) (f16 s' 1)), true)))

@[expose] noncomputable def clsK (w : List Nat) (R P S W : Nat → Nat) (n cnt : Nat) : Bool :=
  bAnd(Nat.beq (R 0) (WK w), bAnd(allN n fun i => bIf(Nat.beq i 0, true, repK R P i),
    bAnd(sortK R S n cnt, jAll n R W)))

end CFSG.KD.HN1408

end
