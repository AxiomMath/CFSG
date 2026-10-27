module

public import Certificates.Kernel.T46K.ChainData
public import Certificates.Data.Kernel.Fi22.T46
public import Certificates.Data.Kernel.Spor.PChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT46

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.T46K

@[expose] noncomputable def rangeK (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun k ih acc => ih (List.cons k acc)) n []

@[expose] noncomputable def QT : List Nat := rangeK (nat_lit 693)

@[expose] noncomputable def BT (i : Nat) : Nat := List.getD [0, 1, 3, 9, 45] i (nat_lit 0)

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0
@[expose] noncomputable def PTST : Nat → Nat → Nat := lvSel [TT0.PTS, TT1.PTS, TT2.PTS, TT3.PTS, TT4.PTS]
@[expose] noncomputable def POST : Nat → Nat → Nat := lvSel [TT0.POS, TT1.POS, TT2.POS, TT3.POS, TT4.POS]
@[expose] noncomputable def PART : Nat → Nat → Nat := lvSel [TT0.PAR, TT1.PAR, TT2.PAR, TT3.PAR, TT4.PAR]
@[expose] noncomputable def LABT : Nat → Nat → Nat := lvSel [TT0.LAB, TT1.LAB, TT2.LAB, TT3.LAB, TT4.LAB]
@[expose] noncomputable def TIT : Nat → Nat → Nat := lvSel [TT0.TI, TT1.TI, TT2.TI, TT3.TI, TT4.TI]
@[expose] noncomputable def CNTT (i : Nat) : Nat :=
  List.getD [TT0.cnt, TT1.cnt, TT2.cnt, TT3.cnt, TT4.cnt] i (nat_lit 0)

@[expose] noncomputable def hdK : Bool :=
  allN (nat_lit 5) fun i => tbfsHdK (nat_lit 693) (BT i) (CNTT i) (PTST i) (POST i) (PART i) (LABT i)

@[expose] noncomputable def ptSl (i c : Nat) : Bool :=
  tbfsSlK (nat_lit 693) (CNTT i) (lvK LK BT (nat_lit 106) i).length LK (lvAt LK BT (nat_lit 106) i)
    (PTST i) (POST i) (PART i) (LABT i) (TIT i) (Nat.mul c (nat_lit 64)) (nat_lit 64)

@[expose] noncomputable def t0Sl (c : Nat) : Bool := ptSl (nat_lit 0) c
@[expose] noncomputable def t1Sl (c : Nat) : Bool := ptSl (nat_lit 1) c

@[expose] noncomputable def t234K : Bool := bAnd(ptSl (nat_lit 2) (nat_lit 0), bAnd(ptSl (nat_lit 2) (nat_lit 1),
  bAnd(ptSl (nat_lit 3) (nat_lit 0), ptSl (nat_lit 4) (nat_lit 0))))

@[expose] noncomputable def sizesK : Bool :=
  bAnd(Nat.beq TT0.cnt (nat_lit 693), bAnd(Nat.beq TT1.cnt (nat_lit 512), bAnd(Nat.beq TT2.cnt (nat_lit 120),
    bAnd(Nat.beq TT3.cnt (nat_lit 36), Nat.beq TT4.cnt (nat_lit 6)))))

end CertificateChecks.KernelT46

end
