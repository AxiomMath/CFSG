module

public import Certificates.Kernel.ONSeven.BDefs
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Kernel.ONSeven.BDefs
public meta import Certificates.Kernel.ONSeven.Gen
public import Certificates.Kernel.ONSeven.Gen

public section

namespace CertificateChecks.KernelSpor.ONS.Gen

meta def ctx : Ctx := mkCtx

meta def aM (r : Nat) : List Nat := aList ctx (cw r)
meta def cM (r : Nat) : List Nat := ccSlices ctx (cw r)
meta def fM (r : Nat) : List Nat := fixSlices ctx (xw r) (tw r) ((bd r).map Prod.fst)
meta def abM (r i : Nat) : List Nat := aList ctx (bw r i)
meta def cbM (r i : Nat) : List Nat := ccSlices ctx (bw r i)

meta def a0 : List Nat := aM 0
meta def a1 : List Nat := aM 1
meta def a2 : List Nat := aM 2
meta def a3 : List Nat := aM 3
meta def a4 : List Nat := aM 4
meta def c0 : List Nat := cM 0
meta def c1 : List Nat := cM 1
meta def c2 : List Nat := cM 2
meta def c3 : List Nat := cM 3
meta def c4 : List Nat := cM 4
meta def f0 : List Nat := fM 0
meta def f1 : List Nat := fM 1
meta def f2 : List Nat := fM 2
meta def f3 : List Nat := fM 3
meta def f4 : List Nat := fM 4
meta def a00 : List Nat := abM 0 0
meta def a01 : List Nat := abM 0 1
meta def a10 : List Nat := abM 1 0
meta def a11 : List Nat := abM 1 1
meta def a20 : List Nat := abM 2 0
meta def a21 : List Nat := abM 2 1
meta def c00 : List Nat := cbM 0 0
meta def c01 : List Nat := cbM 0 1
meta def c10 : List Nat := cbM 1 0
meta def c11 : List Nat := cbM 1 1
meta def c20 : List Nat := cbM 2 0
meta def c21 : List Nat := cbM 2 1

end CertificateChecks.KernelSpor.ONS.Gen

#knatlist CertificateChecks.KernelSpor.ONSB.A0 CertificateChecks.KernelSpor.ONS.Gen.a0
#knatlist CertificateChecks.KernelSpor.ONSB.A1 CertificateChecks.KernelSpor.ONS.Gen.a1
#knatlist CertificateChecks.KernelSpor.ONSB.A2 CertificateChecks.KernelSpor.ONS.Gen.a2
#knatlist CertificateChecks.KernelSpor.ONSB.A3 CertificateChecks.KernelSpor.ONS.Gen.a3
#knatlist CertificateChecks.KernelSpor.ONSB.A4 CertificateChecks.KernelSpor.ONS.Gen.a4
#knatlist CertificateChecks.KernelSpor.ONSB.C0 CertificateChecks.KernelSpor.ONS.Gen.c0
#knatlist CertificateChecks.KernelSpor.ONSB.C1 CertificateChecks.KernelSpor.ONS.Gen.c1
#knatlist CertificateChecks.KernelSpor.ONSB.C2 CertificateChecks.KernelSpor.ONS.Gen.c2
#knatlist CertificateChecks.KernelSpor.ONSB.C3 CertificateChecks.KernelSpor.ONS.Gen.c3
#knatlist CertificateChecks.KernelSpor.ONSB.C4 CertificateChecks.KernelSpor.ONS.Gen.c4
#knatlist CertificateChecks.KernelSpor.ONSB.F0 CertificateChecks.KernelSpor.ONS.Gen.f0
#knatlist CertificateChecks.KernelSpor.ONSB.F1 CertificateChecks.KernelSpor.ONS.Gen.f1
#knatlist CertificateChecks.KernelSpor.ONSB.F2 CertificateChecks.KernelSpor.ONS.Gen.f2
#knatlist CertificateChecks.KernelSpor.ONSB.F3 CertificateChecks.KernelSpor.ONS.Gen.f3
#knatlist CertificateChecks.KernelSpor.ONSB.F4 CertificateChecks.KernelSpor.ONS.Gen.f4
#knatlist CertificateChecks.KernelSpor.ONSB.A00 CertificateChecks.KernelSpor.ONS.Gen.a00
#knatlist CertificateChecks.KernelSpor.ONSB.A01 CertificateChecks.KernelSpor.ONS.Gen.a01
#knatlist CertificateChecks.KernelSpor.ONSB.A10 CertificateChecks.KernelSpor.ONS.Gen.a10
#knatlist CertificateChecks.KernelSpor.ONSB.A11 CertificateChecks.KernelSpor.ONS.Gen.a11
#knatlist CertificateChecks.KernelSpor.ONSB.A20 CertificateChecks.KernelSpor.ONS.Gen.a20
#knatlist CertificateChecks.KernelSpor.ONSB.A21 CertificateChecks.KernelSpor.ONS.Gen.a21
#knatlist CertificateChecks.KernelSpor.ONSB.C00 CertificateChecks.KernelSpor.ONS.Gen.c00
#knatlist CertificateChecks.KernelSpor.ONSB.C01 CertificateChecks.KernelSpor.ONS.Gen.c01
#knatlist CertificateChecks.KernelSpor.ONSB.C10 CertificateChecks.KernelSpor.ONS.Gen.c10
#knatlist CertificateChecks.KernelSpor.ONSB.C11 CertificateChecks.KernelSpor.ONS.Gen.c11
#knatlist CertificateChecks.KernelSpor.ONSB.C20 CertificateChecks.KernelSpor.ONS.Gen.c20
#knatlist CertificateChecks.KernelSpor.ONSB.C21 CertificateChecks.KernelSpor.ONS.Gen.c21

namespace CertificateChecks.KernelSpor.ONS

open CertificateChecks.KernelSpor

@[expose] noncomputable def AL (r : Nat) : List Nat :=
  [ONSB.A0, ONSB.A1, ONSB.A2, ONSB.A3, ONSB.A4].getD r []
@[expose] noncomputable def CL (r : Nat) : List Nat :=
  [ONSB.C0, ONSB.C1, ONSB.C2, ONSB.C3, ONSB.C4].getD r []
@[expose] noncomputable def FL (r : Nat) : List Nat :=
  [ONSB.F0, ONSB.F1, ONSB.F2, ONSB.F3, ONSB.F4].getD r []

@[expose] noncomputable def ABL (r i : Nat) : List Nat :=
  [[ONSB.A00, ONSB.A01], [ONSB.A10, ONSB.A11], [ONSB.A20, ONSB.A21]].getD r [] |>.getD i []
@[expose] noncomputable def CBL (r i : Nat) : List Nat :=
  [[ONSB.C00, ONSB.C01], [ONSB.C10, ONSB.C11], [ONSB.C20, ONSB.C21]].getD r [] |>.getD i []

@[expose] noncomputable def ccR (r s : Nat) : Bool :=
  ccS (WW (cw r)) (fun k => (AL r).getD k 0) (fun s => (CL r).getD s 0) s

@[expose] noncomputable def fxR (r s : Nat) : Bool :=
  fxS (WW (xw r)) (WW (tw r)) (badB r) (fun s => (FL r).getD s 0) s

@[expose] noncomputable def cbR (r i s : Nat) : Bool :=
  ccS (WW (bw r i)) (fun k => (ABL r i).getD k 0) (fun s => (CBL r i).getD s 0) s

@[expose] noncomputable def cfR (r s : Nat) : Bool :=
  cfS (WW (uw r 0)) (WW (invL (uw r 0))) (WW (cw r)) (fun k => (AL r).getD k 0) s

@[expose] noncomputable def cc0S (s : Nat) : Bool := ccR 0 s
@[expose] noncomputable def cc1S (s : Nat) : Bool := ccR 1 s
@[expose] noncomputable def cc2S (s : Nat) : Bool := ccR 2 s
@[expose] noncomputable def cc3S (s : Nat) : Bool := ccR 3 s
@[expose] noncomputable def cc4S (s : Nat) : Bool := ccR 4 s
@[expose] noncomputable def fx0S (s : Nat) : Bool := fxR 0 s
@[expose] noncomputable def fx1S (s : Nat) : Bool := fxR 1 s
@[expose] noncomputable def fx2S (s : Nat) : Bool := fxR 2 s
@[expose] noncomputable def fx3S (s : Nat) : Bool := fxR 3 s
@[expose] noncomputable def fx4S (s : Nat) : Bool := fxR 4 s
@[expose] noncomputable def cb00S (s : Nat) : Bool := cbR 0 0 s
@[expose] noncomputable def cb01S (s : Nat) : Bool := cbR 0 1 s
@[expose] noncomputable def cb10S (s : Nat) : Bool := cbR 1 0 s
@[expose] noncomputable def cb11S (s : Nat) : Bool := cbR 1 1 s
@[expose] noncomputable def cb20S (s : Nat) : Bool := cbR 2 0 s
@[expose] noncomputable def cb21S (s : Nat) : Bool := cbR 2 1 s
@[expose] noncomputable def cf3S (s : Nat) : Bool := cfR 3 s
@[expose] noncomputable def cf4S (s : Nat) : Bool := cfR 4 s

end CertificateChecks.KernelSpor.ONS

end
