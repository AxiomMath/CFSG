module

public import Certificates.Data.Kernel.W4RowFi22W.Defs
public import Certificates.Kernel.W4RowFi22W.Data
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.E2067T

public section

namespace CertificateChecks.KernelW4F22

open CFSG.KC.Enum CFSG.KC.Census CFSG.KC.W4F22 CertificateChecks.KernelSpor

@[expose] noncomputable def LF (k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 2), Fi22CGT.F k,
  nIf(Nat.blt k (nat_lit 8), Fi22ExtT.L (Nat.add (nat_lit 19) k),
  nIf(Nat.blt k (nat_lit 10), List.getD CFSG.KD.W4F22.AI (Nat.sub k (nat_lit 8)) (nat_lit 0),
    Fi22ExtT.L (Nat.add (nat_lit 11) k))))

@[expose] noncomputable def bs : List Nat :=
  [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 6, nat_lit 4]

@[expose] noncomputable def relK (i : Nat) : Bool :=
  relB (nat_lit 12) (nat_lit 8) LF CFSG.KD.W4F22.E bs
    (List.getD CFSG.KD.W4F22.rels i ([], []))

@[expose] noncomputable def movK (i : Nat) : Bool :=
  bAnd(Nat.blt (List.getD CFSG.KD.W4F22.movs i ([], nat_lit 0)).2 (nat_lit 3510),
    movB (nat_lit 12) (nat_lit 8) LF CFSG.KD.W4F22.E (List.getD CFSG.KD.W4F22.movs i ([], nat_lit 0)))

@[expose] noncomputable def invK (k : Nat) : Bool :=
  allN (nat_lit 3510) fun p => strictB (at' (nat_lit 12) (LF k) p) fun q =>
    bAnd(Nat.blt q (nat_lit 3510), Nat.beq (at' (nat_lit 12) (LF (Nat.add (nat_lit 8) k)) q) p)

@[expose] noncomputable def letK : Bool := lettersB CFSG.KD.W4F22.E (nat_lit 16)

@[expose] noncomputable def aOnlyK : Bool :=
  List.all (List.drop (nat_lit 6) CFSG.KD.W4F22.E) fun x =>
    List.all x fun k => Nat.blt (Nat.mod k (nat_lit 8)) (nat_lit 2)

end CertificateChecks.KernelW4F22

end
