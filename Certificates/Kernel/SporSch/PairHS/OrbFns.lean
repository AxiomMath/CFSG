module

public import Certificates.Data.Kernel.SporSch.PairHeCnt
public import Certificates.Kernel.SporSch.PairHS.CntFns
public import Certificates.Kernel.SporSch.PairHS.OrbData

public section

namespace CertificateChecks.KernelSporSch.PHSCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def XRA (j : Nat) : Nat := PHSCl.XA (PHSO.RPA j)

@[expose] noncomputable def XRB (j : Nat) : Nat := PHSCl.XB (PHSO.RPB j)

@[expose] noncomputable def KSA (t : Nat) : Nat := PHSCl.KA (PHSO.SGA t)

@[expose] noncomputable def KSB (t : Nat) : Nat := PHSCl.KB (PHSO.SGB t)

@[expose] noncomputable def orbA (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (fun j => bIf(Nat.blt j (nat_lit 525), heoAt 12 PHST.NR PHST.NR PHST.LT PHST.PT (nat_lit 4)
      (nat_lit 3850) (nat_lit 11) (nat_lit 33) (nat_lit 5) (nat_lit 732192) PHSO.OP bs XRA zP KSA j,
      true)) 64

@[expose] noncomputable def orbB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (fun j => bIf(Nat.blt j (nat_lit 1400), heoAt 12 PHST.NR PHST.NR PHST.LT PHST.PT (nat_lit 4)
      (nat_lit 3850) (nat_lit 11) (nat_lit 33) (nat_lit 5) (nat_lit 732192) PHSO.OP bs XRB zP KSB j,
      true)) 64

@[expose] noncomputable def permA (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 4) r) 512)
    (fun t => bIf(Nat.blt t PHST.c, bAnd(Nat.blt (PHSO.SGA t) PHST.c,
      Nat.beq (PHSO.TUA (PHSO.SGA t)) t), true)) 512

@[expose] noncomputable def permB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 512)
    (fun t => bIf(Nat.blt t PHSU.c, bAnd(Nat.blt (PHSO.SGB t) PHSU.c,
      Nat.beq (PHSO.TUB (PHSO.SGB t)) t), true)) 512

@[expose] noncomputable def opB : Bool :=
  bAnd(allBlk 0 (fun m => bAnd(Nat.blt fld(PHSO.OP, Nat.mul 12 m, mask 12) (nat_lit 3850),
      Nat.beq (zP fld(PHSO.OP, Nat.mul 12 m, mask 12))
        fld(PHSO.OP, Nat.mul 12 (heoIx 11 10 m), mask 12))) 33,
    bAnd(allBlk 0 (fun b => bAnd(Nat.blt fld(732192, Nat.mul 5 b, mask 5) 33,
        Nat.beq fld(PHSO.OP, Nat.mul 12 fld(732192, Nat.mul 5 b, mask 5), mask 12) b)) 4,
    bAnd(allBlk 0 (fun j => Nat.blt (PHSO.RPA j) PHST.c) 525,
      allBlk 0 (fun j => Nat.blt (PHSO.RPB j) PHSU.c) 1400)))

@[expose] noncomputable def opB2 : Bool :=
  allBlk 0 (fun k => allBlk 0 (fun b => Nat.beq (powF ziP k b)
    fld(PHSO.OP, Nat.mul 12 (heoIx 11 k fld(732192, Nat.mul 5 b, mask 5)), mask 12)) 4) 11

@[expose] noncomputable def repB : Bool :=
  bAnd(Nat.beq (sumN 2 (fun q => scAt XRA (nat_lit 525) zP ziP q)) 10,
    Nat.beq (sumN 3 (fun q => scAt XRB (nat_lit 1400) zP ziP q)) 2)

end CertificateChecks.KernelSporSch.PHSCn

end
