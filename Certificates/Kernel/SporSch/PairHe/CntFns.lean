module

public import Certificates.Kernel.SporSch.PairHe.CntData
public import Certificates.Kernel.SporSch.PairHe.S2Fns
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

namespace CertificateChecks.KernelSporSch.PHeCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

@[expose] noncomputable def zP (x : Nat) : Nat := pg 14 (mask 14) PHeN.T0 x

@[expose] noncomputable def ziP (x : Nat) : Nat := pg 14 (mask 14) PHeN.T1 x

@[expose] noncomputable def z3P (x : Nat) : Nat := zP (zP (zP x))

@[expose] noncomputable def z3iP (x : Nat) : Nat := ziP (ziP (ziP x))

@[expose] noncomputable def scAt (X K : Nat → Nat) (c : Nat) (Z ZI : Nat → Nat) (D1 D0 q : Nat) :
    Nat :=
  scanHePR 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT PHeSn.bs c X K Z ZI (nat_lit 8330) D1 D0
    (Nat.mul q (nat_lit 512)) (nat_lit 512)

@[expose] noncomputable def repsB : Bool :=
  bAnd(nfValidK 5 HeC.LR PHeN.n0, bAnd(nfValidK 5 HeC.LR PHeN.n1, bAnd(nfValidK 5 HeC.LR PHeN.n2,
  bAnd(ordPL PHeSn.bs zP 17, bAnd(Nat.beq (zP 0) 1,
  bAnd(eqOnL PHeSn.bs (fun b => zP (ziP b)) (fun x => x),
    eqOnL PHeSn.bs (fun b => PHeSn.nfp PHeN.n2 (zP b)) (fun b => zP (zP (PHeSn.nfp PHeN.n2 b)))))))))

@[expose] noncomputable def bindR (F P lo : Nat) : Bool :=
  allBlk lo (bind5At 8330 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT F P) (nat_lit 833)

@[expose] noncomputable def bindB (g r : Nat) : Bool :=
  bindR (nIf(Nat.beq g 0, PHeN.n0, PHeN.n1)) (nIf(Nat.beq g 0, PHeN.T0, PHeN.T1)) (Nat.mul r 833)

@[expose] noncomputable def fixC (f : Nat → Nat) : Nat :=
  sumN 8330 (fun x => nIf(Nat.beq (f x) x, nat_lit 1, nat_lit 0))

@[expose] noncomputable def fixB : Bool :=
  bAnd(Nat.beq (fixC PHeSn.tAP) 346, Nat.beq (fixC PHeSn.tBP) 42)

end CertificateChecks.KernelSporSch.PHeCn

end
