module

public import Certificates.Data.Kernel.SporSch.PairHeCnt
public import Certificates.Kernel.SporSch.PairJ3.CntFns
public import Certificates.Kernel.SporSch.PairJ3.OrbData

public section

namespace CertificateChecks.KernelSporSch.PJ3Cn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def XR (j : Nat) : Nat := PJ3Cl.X (PJ3O.RP j)

@[expose] noncomputable def KS (t : Nat) : Nat := PJ3Cl.K (PJ3O.SG t)

@[expose] noncomputable def orbB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (fun j => bIf(Nat.blt j (nat_lit 1377), heoAt 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT (nat_lit 4)
      (nat_lit 6156) (nat_lit 19) (nat_lit 38) (nat_lit 6) (nat_lit 5132352) PJ3O.OP bs XR zP KS j,
      true)) 64

@[expose] noncomputable def permB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 4) r) 512)
    (fun t => bIf(Nat.blt t PJ3T.c, bAnd(Nat.blt (PJ3O.SG t) PJ3T.c,
      Nat.beq (PJ3O.TU (PJ3O.SG t)) t), true)) 512

@[expose] noncomputable def opB : Bool :=
  bAnd(allBlk 0 (fun m => bAnd(Nat.blt fld(PJ3O.OP, Nat.mul 13 m, mask 13) (nat_lit 6156),
      Nat.beq (zP fld(PJ3O.OP, Nat.mul 13 m, mask 13))
        fld(PJ3O.OP, Nat.mul 13 (heoIx 19 18 m), mask 13))) 38,
    bAnd(allBlk 0 (fun b => bAnd(Nat.blt fld(5132352, Nat.mul 6 b, mask 6) 38,
        Nat.beq fld(PJ3O.OP, Nat.mul 13 fld(5132352, Nat.mul 6 b, mask 6), mask 13) b)) 4,
      allBlk 0 (fun j => Nat.blt (PJ3O.RP j) PJ3T.c) 1377))

@[expose] noncomputable def opB2 : Bool :=
  allBlk 0 (fun k => allBlk 0 (fun b => Nat.beq (powF zP (Nat.sub 19 k) b)
    fld(PJ3O.OP, Nat.mul 13 (heoIx 19 k fld(5132352, Nat.mul 6 b, mask 6)), mask 13)) 4) 19

@[expose] noncomputable def scR (q : Nat) : Nat :=
  scanR 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT bs (nat_lit 1377) XR zP (Nat.mul q (nat_lit 512))
    (nat_lit 512)

@[expose] noncomputable def repB : Bool := Nat.beq (sumN 3 scR) 3

end CertificateChecks.KernelSporSch.PJ3Cn

end
