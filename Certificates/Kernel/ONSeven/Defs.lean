module

public import Certificates.Kernel.Sporadic.ON.LvData
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.CBComm

public section

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KC.Enum CFSG.KS.TW CFSG.KS.CB
open CertificateChecks.KernelSpor.ON (TT UU stepF invF PARf LABf)

@[expose] noncomputable def WW (w : List Int) (x : Nat) : Nat := w.foldr (GZ TT UU) x

@[expose] noncomputable def iter (F : Nat → Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ acc => F acc) e

@[expose] noncomputable def ccZ (Z A : Nat → Nat) (k : Nat) : Nat :=
  ccF Z A (stepF 1) (invF 1) (PARf 1) (LABf 1) (nat_lit 52136) (stepF 2) (PARf 2) (LABf 2)
    (nat_lit 36) (nat_lit 227759) (nat_lit 100817) k

end CertificateChecks.KernelSpor.ONS

end
