module

public import Certificates.Kernel.J2Cover.K20X
public import Certificates.Kernel.J2Cover.ModelsP2

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.J2Cover.Models

@[expose] noncomputable def pK (i a : Nat) : Nat := nIf(Nat.blt a 128, pg 7 (mask 7) (DP a) i, 0)

@[expose] noncomputable def iK (i a : Nat) : Nat := nIf(Nat.blt a 128, pg 13 (mask 13) (DI a) i, 0)

@[expose] noncomputable def fRK (x : Nat) : Nat := pg 128 (mask 128) FRP x

@[expose] noncomputable def hRK (j x : Nat) : Nat := nIf(Nat.blt j 6, pg 128 (mask 128) (HRP j) x, 0)

@[expose] noncomputable def xr4725 (p : Nat → Bool) : Bool :=
  Bool.xor (xorR (fun k => xorR p (64 * k) 64) 0 73) (xorR p (64 * 73) 53)

@[expose] noncomputable def lmK (k b : Nat) : Nat := nIf(Nat.blt k 3, nIf(Nat.blt b 128, lmul k b, 0), 0)

@[expose] noncomputable def btK (a : Nat) : Nat := nIf(Nat.blt a 128, betaIdx a, 0)

@[expose] noncomputable def itK (a : Nat) : Nat := nIf(Nat.blt a 128, invIdx a, 0)

end CertificateChecks.KernelJ2Cover

end
