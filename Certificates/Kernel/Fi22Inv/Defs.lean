module

public import Certificates.Kernel.Fi22Syl.ChainDefs
public import Certificates.Data.Kernel.Fi22.InvK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22Cent CFSG.KS.Fi22I CertificateChecks.KernelFi22S

@[expose] noncomputable def cntK (F : Nat → Nat) : Nat :=
  foldN (nat_lit 3510) (fun i s => nIf(Nat.beq (F i) i, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def inS (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 54), true, bIf(Nat.beq c (nat_lit 182), true, Nat.beq c (nat_lit 694)))

@[expose] noncomputable def wit1L : List Nat := [63, 369, 374, 131, 466]
@[expose] noncomputable def wit2L : List Nat := [0, 8, 31, 63, 168]

@[expose] noncomputable def fix2 (ws : List Nat) (a b : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun k _ ih => bAnd(Nat.beq (cK k a) a, bAnd(Nat.beq (cK k b) b, ih))) ws

@[expose] noncomputable def mvW (ws : List Nat) (p : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun k _ ih => bIf(Nat.beq (cK k p) p, ih, true)) ws

@[expose] noncomputable def stabK : Bool :=
  bAnd(fix2 wit1L (nat_lit 0) (nat_lit 1), bAnd(fix2 wit2L (nat_lit 0) (nat_lit 8),
  bAnd(Nat.beq (gA (nat_lit 8)) (nat_lit 8), bAnd(bIf(Nat.beq (gA (nat_lit 1)) (nat_lit 8), false, true),
  bAnd(allN (nat_lit 3510) (fun p => bIf(Nat.beq p (nat_lit 0), true, bIf(Nat.beq p (nat_lit 1), true,
    bIf(Nat.beq p (gA (nat_lit 1)), true, mvW wit1L p)))),
  allN (nat_lit 3510) (fun p => bIf(Nat.beq p (nat_lit 0), true, bIf(Nat.beq p (nat_lit 8), true,
    mvW wit2L p))))))))

@[expose] noncomputable def attK (w : List Nat) (c : Nat) : Bool :=
  bAnd(allN (nat_lit 3510) (fun x => Nat.beq (wordK w (wordK w x)) x),
    bAnd(anyMv (wordK w), Nat.beq (cntK (wordK w)) c))

@[expose] noncomputable def attAllK : Bool :=
  bAnd(attK [0] (nat_lit 694), bAnd(attK [0, 8] (nat_lit 182), attK [0, 8, 31] (nat_lit 54)))

@[expose] noncomputable def repChk (r : Nat) : Bool :=
  bAnd(Nat.blt (rpK r) (nat_lit 1024), bAnd(Nat.blt (rpJ r) (nat_lit 128), bAnd(inS (rpC r),
    Nat.beq (cntK (gK (rpK r) (rpJ r))) (rpC r))))

@[expose] noncomputable def repSl (c : Nat) : Bool :=
  bAnd(repChk (Nat.mul (nat_lit 2) c), repChk (Nat.succ (Nat.mul (nat_lit 2) c)))

@[expose] noncomputable def conjQ (D G R : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => bAnd(Nat.beq (strictN (G q) D) (strictN (D q) R), ih)) QL

@[expose] noncomputable def fixLeafK (k j : Nat) : Bool :=
  bIf(anyMv (sq (gK k j)), true, bIf(allFix (gK k j), true,
    strictB (ilR k j) fun r1 => bAnd(Nat.blt (nat_lit 0) r1, strictB (Nat.sub r1 (nat_lit 1)) fun r =>
      bAnd(Nat.blt r (nat_lit 54), bAnd(Nat.blt (ilK k j) (nat_lit 1024),
        bAnd(Nat.blt (ilJ k j) (nat_lit 128),
          conjQ (gK (ilK k j) (ilJ k j)) (gK k j) (gK (rpK r) (rpJ r))))))))

@[expose] noncomputable def fixSl (c : Nat) : Bool :=
  allN (nat_lit 8) fun d => strictB (Nat.add (Nat.mul c (nat_lit 8)) d) fun k =>
    allN (nat_lit 128) fun j => fixLeafK k j

end CertificateChecks.KernelFi22I

end
