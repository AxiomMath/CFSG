module

public import Certificates.Kernel.Fi22Syl.ChainDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Uq

open CFSG.KC.Enum CFSG.KS.Fi22Cent CertificateChecks.KernelFi22S
  CFSG.EvenSporadicStandard.TwoFi22.DS81

@[expose] noncomputable def dK (j x : Nat) : Nat := gK (uqDp[j]!).1 (uqDp[j]!).2 x

@[expose] noncomputable def bK (i x : Nat) : Nat := dK uqBas[i]! x

@[expose] noncomputable def eqQ (F G : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(Nat.beq (F q) (G q), ih)) QL

@[expose] noncomputable def neQ (F G : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun q _ ih => bIf(Nat.beq (F q) (G q), ih, true)) QL

@[expose] noncomputable def phiL (m : Nat) (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i _ ih x => strictN (ih x) fun y => nIf(m.testBit i, bK i y, y)) l

@[expose] noncomputable def phiK (m : Nat) : Nat → Nat := phiL m (List.range 10)

@[expose] noncomputable def c25230leaf : Bool :=
  allN (nat_lit 22) fun j => bAnd(allFix (sq (dK j)),
    bAnd(anyMv (dK j), allFix (cb fun x => strictN (gA x) (dK j))))

@[expose] noncomputable def c25230dist : Bool :=
  allN (nat_lit 22) fun i => allN i fun j => neQ (dK i) (dK j)

@[expose] noncomputable def c25230comm : Bool :=
  allN (nat_lit 10) fun i => allN i fun j =>
    eqQ (fun x => strictN (bK j x) (bK i)) (fun x => strictN (bK i x) (bK j))

@[expose] noncomputable def c25230phi : Bool :=
  allN (nat_lit 22) fun j => eqQ (phiK uqW[j]!) (dK j)

@[expose] noncomputable def actRow (l k : Nat) (r : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 10))
    (fun s _ ih i => bAnd(Nat.blt s (nat_lit 22), bAnd(
      eqQ (fun x => strictN (bK i x) (wP l k)) (fun x => strictN (wP l k x) (dK s)),
      ih (Nat.succ i)))) r

@[expose] noncomputable def c25230act0 (c : Nat) : Bool :=
  allN (nat_lit 64) fun d => strictB (Nat.add (Nat.mul c (nat_lit 64)) d) fun k =>
    actRow (nat_lit 0) k (uqDecode uqSg0S[k]!).toList (nat_lit 0)

@[expose] noncomputable def c25230act1 (c : Nat) : Bool :=
  allN (nat_lit 64) fun d => strictB (Nat.add (Nat.mul c (nat_lit 64)) d) fun k =>
    actRow (nat_lit 1) k (uqDecode uqSg1S[k]!).toList (nat_lit 0)

end CertificateChecks.KernelFi22Uq

end
