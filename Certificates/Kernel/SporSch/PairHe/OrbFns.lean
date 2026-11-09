module

public import Certificates.Kernel.SporSch.PairHe.CntFns
public import Certificates.Kernel.SporSch.PairHe.OrbData

public section

namespace CertificateChecks.KernelSporSch.PHeCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

@[expose] noncomputable def XR (j : Nat) : Nat := PHeCl.XA (PHeO.RP j)

@[expose] noncomputable def KR (j : Nat) : Nat := PHeCl.KA (PHeO.RP j)

@[expose] noncomputable def KS (t : Nat) : Nat := PHeCl.KA (PHeO.SG t)

@[expose] noncomputable def orbB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (fun j => bIf(Nat.blt j (nat_lit 1470), heoAt 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT (nat_lit 5)
      (nat_lit 8330) (nat_lit 17) (nat_lit 17) (nat_lit 5) (nat_lit 2636832) PHeO.OP PHeSn.bs XR zP KS j, true)) 64

@[expose] noncomputable def permB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 7) r) 512)
    (fun t => bIf(Nat.blt t PHeT.c, bAnd(Nat.blt (PHeO.SG t) PHeT.c,
      Nat.beq (PHeO.TU (PHeO.SG t)) t), true)) 512

@[expose] noncomputable def opB : Bool :=
  bAnd(allBlk 0 (fun m => bAnd(Nat.blt fld(PHeO.OP, Nat.mul 14 m, mask 14) (nat_lit 8330),
      Nat.beq (zP fld(PHeO.OP, Nat.mul 14 m, mask 14))
        fld(PHeO.OP, Nat.mul 14 (Nat.mod (Nat.succ m) 17), mask 14))) 17,
    bAnd(Nat.beq fld(PHeO.OP, 0, mask 14) 0,
    bAnd(allBlk 0 (fun b => bAnd(Nat.blt fld(2636832, Nat.mul 5 b, 31) 17,
        Nat.beq fld(PHeO.OP, Nat.mul 14 fld(2636832, Nat.mul 5 b, 31), mask 14) b)) 5,
      allBlk 0 (fun j => Nat.blt (PHeO.RP j) PHeT.c) 1470)))

@[expose] noncomputable def opB2 : Bool :=
  allBlk 0 (fun k => allBlk 0 (fun b => Nat.beq (powF ziP k b)
    fld(PHeO.OP, Nat.mul 14 (Nat.mod (Nat.add fld(2636832, Nat.mul 5 b, 31) (Nat.sub 17 k)) 17),
      mask 14)) 5) 17

@[expose] noncomputable def repB : Bool :=
  bAnd(Nat.beq (sumN 3 (fun q => scAt XR KR (nat_lit 1470) zP ziP (nat_lit 8330) (nat_lit 1) q)) 1,
    Nat.beq (sumN 3 (fun q => scAt XR KR (nat_lit 1470) z3P z3iP (nat_lit 4814819443210000)
      (nat_lit 578009537000) q)) 1)

end CertificateChecks.KernelSporSch.PHeCn

end
