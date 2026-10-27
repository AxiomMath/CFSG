module

public import Certificates.Kernel.HN1408.TableKData
public import Certificates.Kernel.HN1408.Words
public import Certificates.Data.Kernel.Spor.MulHQ

public section

namespace CFSG.KD.HN1408.TK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KD.HN1408
open CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def powK (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ ih => strictN ih fun Y => pc Y X) e

@[expose] noncomputable def specK (G : Nat → Nat) (sp : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) idK
    (fun p _ ih => strictN ih fun Y => pc (powK (G (Nat.sub p.1 1)) p.2) Y) sp

@[expose] noncomputable def uK (l : Nat) : Nat := WK (classz.centGens.getD l [])

@[expose] noncomputable def kK (l : Nat) : Nat := specK uK (kSpec.getD l [])

@[expose] noncomputable def nK (j : Nat) : Nat := specK kK (nSpecK.getD j [])

@[expose] noncomputable def swapsK (p : Nat) : Bool :=
  allN 704 fun k => bAnd(Nat.ble 704 (pt p k), Nat.blt (pt p (704 + k)) 704)

@[expose] noncomputable def headR (GT : Nat → Nat) (k m : Nat) (G GI GJ T PL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(allN k fun j => bAnd(Nat.beq (GI j) (GT j),
    bAnd(Nat.beq (G j) idK, bAnd(canonK 1408 11 (mask 11) (1408 * 11) (GJ j),
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j)))),
    bAnd(Nat.beq cnt m, penumHdK idK cnt 100000 T PL))

@[expose] noncomputable def recK (k cnt : Nat) (G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat) :
    Bool :=
  bAnd(penumSlK 1408 11 (mask 11) (1408 * 11) true G GI k cnt T PL POS SRT SRI 0 cnt,
    bAnd(slK cnt (hsortPtK 1408 11 (mask 11) cnt T HS HSI) 0 cnt,
      slK (Nat.mul cnt (Nat.add k k))
        (findPtK cnt T (prodQK 1408 11 (mask 11) (Nat.add k k) T (bothK k GI GJ)) CL) 0
        (Nat.mul cnt (Nat.add k k))))

@[expose] noncomputable def qCentK (C i : Nat) : Bool :=
  strictB (TKQW i) fun w => strictB (TKQ.T i) fun s =>
    bIf(Nat.blt w 4, bIf(commP s (TKQ.GI w), false, true),
      bIf(Nat.beq w 4, Nat.beq s idK, bAnd(Nat.beq w 5, Nat.beq s C)))

@[expose] noncomputable def qCommK (C i : Nat) : Bool :=
  strictB (TKQ.T i) fun s => allN 32 fun j => strictB (TKQ.T j) fun t =>
    strictB (pc s t) fun st => strictB (pc t s) fun ts =>
      bIf(Nat.beq st ts, true, Nat.beq st (pc C ts))

@[expose] noncomputable def qSqK (C i : Nat) : Bool :=
  strictB (TKQ.T i) fun s => strictB (pc s s) fun q =>
    bIf(Nat.beq q idK, true, Nat.beq q C)

end CFSG.KD.HN1408.TK

end
