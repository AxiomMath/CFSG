module

public import Certificates.Kernel.U38R.Checks
public import Certificates.Kernel.U38R.ElimData
public import Certificates.Data.Kernel.U38ElimK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38R

open CFSG.KC.Enum CFSG.KS CFSG.KC.U38Elim

@[expose] noncomputable def eX (i : Nat) : Bool := Nat.beq (ixBit i) (nat_lit 1)

@[expose] noncomputable def eComm (i j : Nat) : Bool := Nat.beq (mulK i j) (mulK j i)

@[expose] noncomputable def eCube (i : Nat) : Bool := Nat.beq (mulK i (mulK i i)) (nat_lit 0)

@[expose] noncomputable def eBel (i1 i2 : Nat) : List Nat :=
  [0, i1, mulK i1 i1, i2, mulK i1 i2, mulK (mulK i1 i1) i2, mulK i2 i2, mulK i1 (mulK i2 i2),
    mulK (mulK i1 i1) (mulK i2 i2)]

@[expose] noncomputable def eBK (B : Nat → Nat) (k t : Nat) : Nat := pg 10 (nat_lit 1023) (B k) t

@[expose] def e185WJ : List Nat :=
  [702, 402, 250, 418, 393, 356, 310, 345, 307, 370, 337, 705, 313, 707, 388, 713, 297, 369]

@[expose] def e185WL : List Nat := [247, 263, 282]

@[expose] noncomputable def e185S3K (S : List Nat) : Bool :=
  allN 729 fun i => bIf(bAnd(eX i, bAnd(!(Nat.beq i 0), eCube i)), eMem i S, true)

@[expose] noncomputable def e185S3InK (S : List Nat) : Bool :=
  eAll (fun s => bAnd(Nat.blt s 729, eX s)) S

@[expose] noncomputable def e185CMK (S : List Nat) (C : Nat → Nat) : Bool :=
  eAll (fun i => allN 729 fun x =>
    Bool.rec (motive := fun _ => Bool) (!(eBit (C i) x)) (eBit (C i) x) (eComm x i)) S

@[expose] noncomputable def e185D1K (S : List Nat) (C : Nat → Nat) : Bool :=
  allN 729 fun j => bIf(eX j, true, eAny (fun s => !(eBit (C s) j)) S)

@[expose] noncomputable def e185PairK (C P N B : Nat → Nat) (i1 i2 : Nat) : Bool :=
  strictB (pg 4 (nat_lit 15) (P i1) i2) fun k =>
    bAnd(Nat.beq (Nat.land (C i1) (C i2)) (N k), allN 9 fun t => eMem (eBK B k t) (eBel i1 i2))

@[expose] noncomputable def e185PairsK (S : List Nat) (C P N B : Nat → Nat) : Bool :=
  eAll (fun i1 => eAll (fun i2 =>
    bIf(bAnd(eBit (C i2) i1, bAnd(!(Nat.beq i2 i1), !(Nat.beq i2 (mulK i1 i1)))),
      e185PairK C P N B i1 i2, true)) S) S

@[expose] noncomputable def e185RefK (N B : Nat → Nat) (k j t : Nat) : Bool :=
  strictB (eBK B k t) fun b =>
    allN 729 fun x => bIf(eBit (N k) x, !(Nat.beq (mulK x j) (mulK (mulK b j) x)), true)

@[expose] noncomputable def e185OmK (B : Nat → Nat) (k j : Nat) : Bool :=
  bAnd(eMem j e185WJ, eAll (fun l => eAnyN 9 fun t => Nat.beq (eBK B k t) l) e185WL)

@[expose] noncomputable def e185KeysK (N B W : Nat → Nat) : Bool :=
  allN 16 fun k => allN 729 fun j =>
    bIf(bAnd(eBit (N k) j, bAnd(!(eX j), eCube j)),
      strictB (pg 4 (nat_lit 15) (W k) j) fun t =>
        bIf(Nat.blt t 9, e185RefK N B k j t, e185OmK B k j),
      true)

@[expose] noncomputable def eP (p q : Nat) : Nat := pcomp 513 10 (mask 10) p q

@[expose] noncomputable def eCj (h a : Nat) : Nat := eP h (eP a (pinvS 513 10 (mask 10) h))

@[expose] noncomputable def witK (hi j : Nat) : Bool :=
  strictB (RH.F (Nat.add 3 hi)) fun H =>
  strictB (eP (eCj H (UR.T 247)) (UR.T 263)) fun z1 =>
  strictB (eP (UR.T 247) (eP (eCj H (UR.T 263)) (UR.T 282))) fun z2 =>
  strictB (eP z1 z2) fun p =>
    bAnd(Nat.blt hi 9, bAnd(Nat.beq (eP H (UR.T j)) (eP (UR.T j) H),
      bAnd(Nat.beq (eP (eP z1 z1) (eP z1 z1)) (pidn 513 10),
      bAnd(Nat.beq (eP (eP z2 z2) (eP z2 z2)) (pidn 513 10),
      bAnd(Nat.beq (eP p (eP p p)) (pidn 513 10), !(Nat.beq p (pidn 513 10)))))))

theorem e185S3 : e185S3K S3L = true := by quickRfl

theorem e185S3In : e185S3InK S3L = true := by quickRfl

theorem e185CM : e185CMK S3L CM = true := by quickRfl

theorem e185D1 : e185D1K S3L CM = true := by quickRfl

theorem e185Pairs : e185PairsK S3L CM PK CN BK = true := by quickRfl

theorem e185Keys : e185KeysK CN BK TW = true := by quickRfl

theorem e185Wit : allN 18 (fun m => witK (Nat.div m 2) (List.getD e185WJ m 0)) = true := by
  quickRfl

end CertificateChecks.KernelU38R

end
