module

public import Certificates.Kernel.HS3850.F25371

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN

@[expose] noncomputable def cmAt (a b p : Nat) : Bool :=
  Nat.beq (img a (img b p)) (img b (img a p))

@[expose] noncomputable def tpts (f : Nat → Bool) : Bool :=
  bAnd(f (nat_lit 517), bAnd(f (nat_lit 1001), bAnd(f (nat_lit 1597), bAnd(f (nat_lit 2003),
    bAnd(f (nat_lit 2689), f (nat_lit 3011))))))

@[expose] noncomputable def cmQ (a b : Nat) : Bool :=
  bAnd(tpts (cmAt a b), cmK a b)

@[expose] noncomputable def cmAt2 (w x g p : Nat) : Bool :=
  Nat.beq (img w (img x (img g p))) (img g (img w (img x p)))

@[expose] noncomputable def cmP2 (w x g : Nat) : Bool := tpts (cmAt2 w x g)

@[expose] noncomputable def sqAtQ (w g0 g1 x : Nat) : Bool :=
  bAnd(bIf(bAnd(cmQ x g0, cmQ x g1), sqK x, true),
    bIf(bAnd(cmP2 w x g0, cmP2 w x g1),
      strictB (pc w x) (fun wx => bIf(bAnd(cmK wx g0, cmK wx g1), sqK wx, true)), true))

@[expose] noncomputable def ptFQ (w a0 a1 b0 b1 e0 e1 e2 i : Nat) : Bool :=
  strictB (A.T i) (fun x =>
    bAnd(sqAtQ w a0 a1 x, bAnd(sqAtQ w b0 b1 x,
      Bool.beq (bAnd(cmQ x e0, bAnd(cmQ x e1, cmQ x e2))) (t0Idx.elem i))))

@[expose] noncomputable def ckFB (w a0 a1 b0 b1 e0 e1 e2 s : Nat) : Bool :=
  allN 32 (fun d => strictB (Nat.add (Nat.mul s (nat_lit 32)) d) (fun i =>
    bIf(Nat.blt i (nat_lit 7680), ptFQ w a0 a1 b0 b1 e0 e1 e2 i, true)))

@[expose] noncomputable def ckFq (s : Nat) : Bool :=
  strictB (FT.F 0) fun w => strictB (lc1 0) fun a0 => strictB (lc1 1) fun a1 =>
  strictB oc0K fun b0 => strictB oc1K fun b1 => strictB (ET0.G 0) fun e0 =>
  strictB (ET0.G 1) fun e1 => strictB (ET0.G 2) fun e2 =>
  allN 8 (fun c => ckFB w a0 a1 b0 b1 e0 e1 e2 (Nat.add (Nat.mul s (nat_lit 8)) c))

end CFSG.KD.HS3850

#kqb_range CFSG.KD.HS3850.EFq CFSG.KD.HS3850.ckFq 0 30

end
