module

public import Certificates.Kernel.ONSeven.BData

public section

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KS.ON (tab)

@[expose] noncomputable def lnX0 (p : Nat) : Nat :=
  tab ONV.T6 (tab ONV.T3 (tab ONV.U5 (tab ONV.U6 (tab ONV.T3 (tab ONV.U5 p)))))
@[expose] noncomputable def lnX1 (p : Nat) : Nat :=
  tab ONV.T6 (tab ONV.T3 (tab ONV.T3 (tab ONV.T6 (tab ONV.T3 (tab ONV.T3 p)))))
@[expose] noncomputable def lnX2 (p : Nat) : Nat :=
  tab ONV.T2 (tab ONV.T2 (tab ONV.T5 (tab ONV.U6 (tab ONV.U2 (tab ONV.T6 p)))))
@[expose] noncomputable def lnX3 (p : Nat) : Nat := tab ONV.U2 (tab ONV.U4 (tab ONV.U3 (tab ONV.T4 p)))
@[expose] noncomputable def lnX4 (p : Nat) : Nat :=
  tab ONV.T3 (tab ONV.U4 (tab ONV.U2 (tab ONV.T5 (tab ONV.T2 p))))
@[expose] noncomputable def cjT0 (p : Nat) : Nat :=
  tab ONV.U0 (tab ONV.U3 (tab ONV.U5 (tab ONV.T3 (tab ONV.U6 (tab ONV.T4 p)))))
@[expose] noncomputable def cjT1 (p : Nat) : Nat :=
  tab ONV.U0 (tab ONV.U5 (tab ONV.T2 (tab ONV.T5 (tab ONV.U4 (tab ONV.U2 p)))))

@[expose] noncomputable def cjI0 (p : Nat) : Nat :=
  tab ONV.U4 (tab ONV.T6 (tab ONV.U3 (tab ONV.T5 (tab ONV.T3 (tab ONV.A p)))))
@[expose] noncomputable def cjI1 (p : Nat) : Nat :=
  tab ONV.T2 (tab ONV.T4 (tab ONV.U5 (tab ONV.U2 (tab ONV.T5 (tab ONV.A p)))))
@[expose] noncomputable def cwC0 (p : Nat) : Nat := cjT0 (lnX0 (cjI0 p))
@[expose] noncomputable def cwC1 (p : Nat) : Nat := cjT1 (lnX1 (cjI1 p))
@[expose] noncomputable def ubW00 (p : Nat) : Nat := tab ONV.A p
@[expose] noncomputable def ubI00 (p : Nat) : Nat := tab ONV.U0 p
@[expose] noncomputable def ubW01 (p : Nat) : Nat :=
  tab ONV.A (tab ONV.U1 (tab ONV.A (tab ONV.B p)))
@[expose] noncomputable def ubI01 (p : Nat) : Nat :=
  tab ONV.U1 (tab ONV.U0 (tab ONV.B (tab ONV.U0 p)))
@[expose] noncomputable def ubW20 (p : Nat) : Nat :=
  tab ONV.U5 (tab ONV.U3 (tab ONV.B (tab ONV.T6 (tab ONV.A p))))
@[expose] noncomputable def ubI20 (p : Nat) : Nat :=
  tab ONV.U0 (tab ONV.U6 (tab ONV.U1 (tab ONV.T3 (tab ONV.T5 p))))
@[expose] noncomputable def ubW21 (p : Nat) : Nat :=
  tab ONV.T6 (tab ONV.U2 (tab ONV.U4 (tab ONV.A p)))
@[expose] noncomputable def ubI21 (p : Nat) : Nat :=
  tab ONV.U0 (tab ONV.T4 (tab ONV.T2 (tab ONV.U6 p)))
@[expose] noncomputable def ubW30 (p : Nat) : Nat := tab ONV.U1 (tab ONV.A (tab ONV.B p))
@[expose] noncomputable def ubI30 (p : Nat) : Nat := tab ONV.U1 (tab ONV.U0 (tab ONV.B p))
@[expose] noncomputable def bwC00 (p : Nat) : Nat := ubI00 (cwC0 (ubW00 p))
@[expose] noncomputable def bwC01 (p : Nat) : Nat := ubI01 (cwC0 (ubW01 p))
@[expose] noncomputable def bwC10 (p : Nat) : Nat := ubI00 (cwC1 (ubW00 p))
@[expose] noncomputable def bwC11 (p : Nat) : Nat := ubI01 (cwC1 (ubW01 p))
@[expose] noncomputable def bwC20 (p : Nat) : Nat := ubI20 (lnX2 (ubW20 p))
@[expose] noncomputable def bwC21 (p : Nat) : Nat := ubI21 (lnX2 (ubW21 p))

@[expose] noncomputable def cd0S (s : Nat) : Bool :=
  ccS cwC0 (fun k => (AL 0).getD k 0) (fun s => (CL 0).getD s 0) s
@[expose] noncomputable def cd1S (s : Nat) : Bool :=
  ccS cwC1 (fun k => (AL 1).getD k 0) (fun s => (CL 1).getD s 0) s
@[expose] noncomputable def cd2S (s : Nat) : Bool :=
  ccS lnX2 (fun k => (AL 2).getD k 0) (fun s => (CL 2).getD s 0) s
@[expose] noncomputable def cd3S (s : Nat) : Bool :=
  ccS lnX3 (fun k => (AL 3).getD k 0) (fun s => (CL 3).getD s 0) s
@[expose] noncomputable def cd4S (s : Nat) : Bool :=
  ccS lnX4 (fun k => (AL 4).getD k 0) (fun s => (CL 4).getD s 0) s
@[expose] noncomputable def ch00S (s : Nat) : Bool :=
  ccS bwC00 (fun k => (ABL 0 0).getD k 0) (fun s => (CBL 0 0).getD s 0) s
@[expose] noncomputable def ch01S (s : Nat) : Bool :=
  ccS bwC01 (fun k => (ABL 0 1).getD k 0) (fun s => (CBL 0 1).getD s 0) s
@[expose] noncomputable def ch10S (s : Nat) : Bool :=
  ccS bwC10 (fun k => (ABL 1 0).getD k 0) (fun s => (CBL 1 0).getD s 0) s
@[expose] noncomputable def ch11S (s : Nat) : Bool :=
  ccS bwC11 (fun k => (ABL 1 1).getD k 0) (fun s => (CBL 1 1).getD s 0) s
@[expose] noncomputable def ch20S (s : Nat) : Bool :=
  ccS bwC20 (fun k => (ABL 2 0).getD k 0) (fun s => (CBL 2 0).getD s 0) s
@[expose] noncomputable def ch21S (s : Nat) : Bool :=
  ccS bwC21 (fun k => (ABL 2 1).getD k 0) (fun s => (CBL 2 1).getD s 0) s
@[expose] noncomputable def cq3S (s : Nat) : Bool :=
  cfS ubW30 ubI30 lnX3 (fun k => (AL 3).getD k 0) s
@[expose] noncomputable def cq4S (s : Nat) : Bool :=
  cfS ubW30 ubI30 lnX4 (fun k => (AL 4).getD k 0) s

@[expose] noncomputable def fy0S (s : Nat) : Bool := fxS lnX0 cjT0 (badB 0) (fun s => (FL 0).getD s 0) s
@[expose] noncomputable def fy1S (s : Nat) : Bool := fxS lnX1 cjT1 (badB 1) (fun s => (FL 1).getD s 0) s
@[expose] noncomputable def fy2S (s : Nat) : Bool :=
  fxS lnX2 (fun p => p) (badB 2) (fun s => (FL 2).getD s 0) s
@[expose] noncomputable def fy3S (s : Nat) : Bool :=
  fxS lnX3 (fun p => p) (badB 3) (fun s => (FL 3).getD s 0) s
@[expose] noncomputable def fy4S (s : Nat) : Bool :=
  fxS lnX4 (fun p => p) (badB 4) (fun s => (FL 4).getD s 0) s

end CertificateChecks.KernelSpor.ONS

end
