module

public import Certificates.Kernel.G24B.Recs
public import Certificates.Kernel.G24B.BData
public import Certificates.Data.Kernel.G24Wit.K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.KC.Misc.G24 CFSG.KC.F2BfsRec CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Quasithin.St84.G24Ident

@[expose] noncomputable def bX (k : Nat) : Nat := wordF4 CFSG.KD.Misc.G24.Gb (parseK (nthL CFSG.KD.Misc.G24.XS k))

@[expose] noncomputable def bY (k : Nat) : Nat := wordF4 CFSG.KD.Misc.G24.Gb (parseK (nthL CFSG.KD.Misc.G24.YS k))

@[expose] noncomputable def bN (i : Nat) : Nat :=
  mulF2 28 (bX (Nat.add (Nat.mul 4 i) 1))
    (mulF2 28 (bY (Nat.add (Nat.mul 4 i) 1)) (bX (Nat.add (Nat.mul 4 i) 1)))

@[expose] noncomputable def bH (i : Nat) : Nat :=
  mulF2 28 (bX (Nat.add (Nat.mul 4 i) 2)) (mulF2 28 (bY (Nat.add (Nat.mul 4 i) 3))
    (mulF2 28 (bX (Nat.add (Nat.mul 4 i) 2)) (bN i)))

@[expose] noncomputable def gK : List Nat := [blowW k1, blowW k2, blowW xa, blowW xb]

@[expose] noncomputable def gMK (n : Nat) : List Nat := [blowW k1, blowW k2, blowW xa, blowW xb, n]

@[expose] noncomputable def gMiK (n : Nat) : List Nat :=
  [mulF2 28 (blowW k1) (blowW k1), mulF2 28 (blowW k2) (blowW k2), blowW xa, blowW xb, n]

@[expose] noncomputable def ord3K (X : Nat) : Bool :=
  andB (Nat.beq (mulF2 28 (mulF2 28 X X) X) (oneF2 28)) (notB (Nat.beq X (oneF2 28)))

@[expose] noncomputable def ord2K (X : Nat) : Bool :=
  andB (Nat.beq (mulF2 28 X X) (oneF2 28)) (notB (Nat.beq X (oneF2 28)))

@[expose] noncomputable def commK (X Y : Nat) : Bool := Nat.beq (mulF2 28 X Y) (mulF2 28 Y X)

@[expose] noncomputable def gensK : Bool :=
  andB ((CFSG.Quasithin.St84.G24DC.Native.gBN ()).toList.all fun A => shape4 (CFSG.KC.G24Wit.digsN A)) <|
  andB (gK == CFSG.KC.G24Wit.gbK) <|
  andB (Nat.beq (blowW k1) (mulF2 28 (bH 0) (mulF2 28 (bH 0) (bH 1)))) <|
  andB (Nat.beq (blowW k2) (bH 1)) <|
  andB (Nat.beq (blowW xa) (bX 5)) <|
  andB (Nat.beq (blowW xb) (bX 1)) <|
  andB (ord3K (blowW k1)) <| andB (ord3K (blowW k2)) <|
  andB (ord2K (blowW xa)) <| andB (ord2K (blowW xb)) <|
  andB (Nat.beq (mulF2 28 (bN 0) (bN 0)) (oneF2 28)) <|
  andB (Nat.beq (mulF2 28 (bN 1) (bN 1)) (oneF2 28)) <|
  andB (commK (blowW k1) (blowW k2)) <| andB (commK (blowW k1) (blowW xa))
    (commK (blowW k2) (blowW xb))

@[expose] noncomputable def paraK (EQ EA : Nat → Nat) (GQ GA : List Nat) (n : Nat)
    (pcB aM dq da : List (List Nat)) (nm dj : List Nat) : Bool :=
  andB (allN 10 fun j => Nat.beq (nthV GQ j) (wordF4 gK (nthL pcB j))) <|
  andB (allN 3 fun t => Nat.beq (nthV GA t) (wordF4 (gMK n) (nthL aM t))) <|
  andB (allN 5 fun x => Nat.beq (nthV (gMK n) x)
    (mulF2 28 (wordF4 GQ (nthL dq x)) (wordF4 GA (nthL da x)))) <|
  andB (allN 180 fun s => strictB (sortedAt 28 12 6 3 EA s) fun X =>
    bIf(Nat.beq X (oneF2 28), true, gapK 28 12 6 10 EQ 1024 (nthV dj s) X))
  (allN 5 fun x => allN 10 fun j => strictB (nthV nm (Nat.add (Nat.mul 10 x) j)) fun s =>
    andB (Nat.blt s 1024) (Nat.beq (sortedAt 28 12 6 10 EQ s)
      (mulF2 28 (mulF2 28 (nthV (gMK n) x) (nthV GQ j)) (nthV (gMiK n) x))))

@[expose] noncomputable def e2K : Nat :=
  mulF2 28 (mulF2 28 (blowW k2) (blowW xa)) (mulF2 28 (blowW k2) (blowW k2))

@[expose] noncomputable def csK : List Nat := [oneF2 28, blowW xa, e2K, mulF2 28 (blowW xa) e2K]

@[expose] noncomputable def cosK (cs : List Nat) : Bool :=
  andB (allN 4 fun i => Nat.beq (mulF2 28 (nthV csK i) (nthV csK i)) (oneF2 28)) <|
  andB (gapK 28 12 6 10 EQ1.CF 1024 (nthV cs 0) (mulF2 28 (nthV csK 0) (nthV csK 1))) <|
  andB (gapK 28 12 6 10 EQ1.CF 1024 (nthV cs 1) (mulF2 28 (nthV csK 0) (nthV csK 2))) <|
  andB (gapK 28 12 6 10 EQ1.CF 1024 (nthV cs 2) (mulF2 28 (nthV csK 0) (nthV csK 3))) <|
  andB (gapK 28 12 6 10 EQ1.CF 1024 (nthV cs 3) (mulF2 28 (nthV csK 1) (nthV csK 2))) <|
  andB (gapK 28 12 6 10 EQ1.CF 1024 (nthV cs 4) (mulF2 28 (nthV csK 1) (nthV csK 3)))
    (gapK 28 12 6 10 EQ1.CF 1024 (nthV cs 5) (mulF2 28 (nthV csK 2) (nthV csK 3)))

theorem ch733008_gens : gensK = true := by quickRfl

theorem ch733008_para1 : paraK EQ1.CF EA1.CF GQ1 GA1 (bN 1) pcB1 aM1 dq1 da1 nm1 dj1 = true := by
  quickRfl

theorem ch733008_para2 : paraK EQ2.CF EA2.CF GQ2 GA2 (bN 0) pcB2 aM2 dq2 da2 nm2 dj2 = true := by
  quickRfl

theorem ch733008_cosets : cosK cs1 = true := by quickRfl

theorem ch733008_negGap : (!paraK EQ1.CF EA1.CF GQ1 GA1 (bN 1) pcB1 aM1 dq1 da1 nm1 dj2) = true := by
  quickRfl

theorem ch733008_negConj :
    (!paraK EQ1.CF EA1.CF GQ1 GA1 (bN 1) pcB1 aM1 dq1 da1 nm2 dj1) = true := by
  quickRfl

theorem ch733008_negWords :
    (!paraK EQ1.CF EA1.CF GQ1 GA1 (bN 1) pcB1 aM2 dq1 da1 nm1 dj1) = true := by
  quickRfl

theorem ch733008_negCos : (!cosK (cs1.map Nat.succ)) = true := by quickRfl

end CFSG.KD.G24B

end
