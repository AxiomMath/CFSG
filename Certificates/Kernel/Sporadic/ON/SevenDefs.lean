module

public import Certificates.Kernel.Sporadic.ON.LvData
public import CFSG.Certificates.Kernel.Spor.CBComm

public section

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS.CB

@[expose] noncomputable def ccX (k : Nat) : Nat :=
  ccF (TT 5) (fun _ => 227759) (stepF 1) (invF 1) (PARf 1) (LABf 1) 52136 (stepF 2) (PARf 2)
    (LABf 2) 36 227759 100817 k

@[expose] noncomputable def ccV (s : Nat) : Nat :=
  List.getD [9, 0, 9, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] s 0

@[expose] noncomputable def ccOK (s : Nat) : Bool :=
  Nat.beq (sumR2 ccX (Nat.mul 2048 s) 32) (ccV s)

@[expose] noncomputable def fxF (q : Nat) : Nat :=
  nIf(Nat.blt q 245520, nIf(Nat.beq (TT 5 q) q, 1, 0), 0)

@[expose] noncomputable def fxV (s : Nat) : Nat := List.getD [20, 15, 10, 8, 11, 5, 13, 8] s 0

@[expose] noncomputable def fxOK (s : Nat) : Bool :=
  Nat.beq (sumR2 fxF (Nat.mul 30720 s) 480) (fxV s)

@[expose] noncomputable def cuOK (s : Nat) : Bool :=
  allN 30690 fun d => (fun q => Nat.beq (TT 5 (TT 5 (TT 5 q))) q) (Nat.add (Nat.mul s 30690) d)

end CertificateChecks.KernelSpor.ON

end
