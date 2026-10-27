module

public import Certificates.Kernel.Fi22Core.ChainData
public import Certificates.Data.Kernel.Fi22.Letters
public import Certificates.Data.Kernel.Spor.PChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.Fi22L

@[expose] noncomputable def LJ (l x : Nat) : Nat := LJk ljPacked slpPacked l x

@[expose] noncomputable def BJ (i : Nat) : Nat := List.getD [0, 1, 6, 11, 3] i (nat_lit 0)

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0
@[expose] noncomputable def PTSJ : Nat → Nat → Nat := lvSel [CT0.PTS, CT1.PTS, CT2.PTS, CT3.PTS, CT4.PTS]
@[expose] noncomputable def POSJ : Nat → Nat → Nat := lvSel [CT0.POS, CT1.POS, CT2.POS, CT3.POS, CT4.POS]
@[expose] noncomputable def PARJ : Nat → Nat → Nat := lvSel [CT0.PAR, CT1.PAR, CT2.PAR, CT3.PAR, CT4.PAR]
@[expose] noncomputable def LABJ : Nat → Nat → Nat := lvSel [CT0.LAB, CT1.LAB, CT2.LAB, CT3.LAB, CT4.LAB]
@[expose] noncomputable def TIJ : Nat → Nat → Nat := lvSel [CT0.TI, CT1.TI, CT2.TI, CT3.TI, CT4.TI]
@[expose] noncomputable def CNTJ (i : Nat) : Nat :=
  List.getD [CT0.cnt, CT1.cnt, CT2.cnt, CT3.cnt, CT4.cnt] i (nat_lit 0)

@[expose] noncomputable def QL : List Nat := [0, 1, 3, 6, 11, 17, 28, 44, 66, 103, 155, 238, 362]

@[expose] noncomputable def QB (i : Nat) : Nat := List.getD [0, 1, 3, 4, 2] i (nat_lit 0)

@[expose] noncomputable def hdK : Bool :=
  allN (nat_lit 5) fun i => tbfsHdK (nat_lit 3510) (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i)

@[expose] noncomputable def ptSl (i c : Nat) : Bool :=
  tbfsSlK (nat_lit 3510) (CNTJ i) (lvK LJ BJ (nat_lit 32) i).length LJ (lvAt LJ BJ (nat_lit 32) i)
    (PTSJ i) (POSJ i) (PARJ i) (LABJ i) (TIJ i) (Nat.mul c (nat_lit 64)) (nat_lit 64)

@[expose] noncomputable def t0Sl (c : Nat) : Bool := ptSl (nat_lit 0) c
@[expose] noncomputable def t1Sl (c : Nat) : Bool := ptSl (nat_lit 1) c
@[expose] noncomputable def t2Sl (c : Nat) : Bool := ptSl (nat_lit 2) c
@[expose] noncomputable def t34K : Bool := bAnd(ptSl (nat_lit 3) (nat_lit 0), bAnd(ptSl (nat_lit 3) (nat_lit 1),
  ptSl (nat_lit 4) (nat_lit 0)))

@[expose] noncomputable def u2Hd : Bool :=
  tbfsHdK (nat_lit 3510) (nat_lit 8) T2.cnt T2.PTS T2.POS T2.PAR T2.LAB

@[expose] noncomputable def u2Sl (c : Nat) : Bool :=
  tbfsSlK (nat_lit 3510) T2.cnt (lvK LJ BJ (nat_lit 32) (nat_lit 1)).length LJ (lvAt LJ BJ (nat_lit 32) (nat_lit 1))
    T2.PTS T2.POS T2.PAR T2.LAB T2.TI (Nat.mul c (nat_lit 64)) (nat_lit 64)

@[expose] noncomputable def coverK : Bool :=
  allN (nat_lit 3510) fun p => bIf(Nat.beq p (nat_lit 0), true,
    bIf(bAnd(Nat.blt (r32 CT1.POS p) CT1.cnt, Nat.beq (r32 CT1.PTS (r32 CT1.POS p)) p), true,
      bAnd(Nat.blt (r32 T2.POS p) (nat_lit 693), Nat.beq (r32 T2.PTS (r32 T2.POS p)) p)))

@[expose] noncomputable def sizesK : Bool :=
  bAnd(Nat.beq CT0.cnt (nat_lit 3510), bAnd(Nat.beq CT1.cnt (nat_lit 2816), bAnd(Nat.beq CT2.cnt (nat_lit 1680),
    bAnd(Nat.beq CT3.cnt (nat_lit 108), bAnd(Nat.beq CT4.cnt (nat_lit 36), Nat.beq T2.cnt (nat_lit 693))))))

end CertificateChecks.KernelFi22C

end
