module

public import Certificates.Kernel.SL4Mod.Data
public import Certificates.Data.Kernel.SL4ModCerts

public section

namespace CertificateChecks.KernelSL4Mod

open CFSG.LargeExtraspecial.SL4Mod.Native

@[expose] noncomputable def cd : Nat → CosetData
  | 0 => { words := W0, codes := #[], invs := #[], tau := T0, fac := F0 }
  | 1 => { words := W1, codes := #[], invs := #[], tau := T1, fac := F1 }
  | _ => { words := W2, codes := #[], invs := #[], tau := T2, fac := F2 }

@[expose] noncomputable def mkOrb (x : Array Nat × Array Nat × Array Nat) : OrbData :=
  { par := x.1, lab := x.2.1, orep := x.2.2 }

@[expose] noncomputable def od : Nat → Nat → OrbData
  | 0, 0 => mkOrb O00
  | 0, 1 => mkOrb O01
  | 0, _ => mkOrb O02
  | 1, 0 => mkOrb O10
  | 1, 1 => mkOrb O11
  | 1, _ => mkOrb O12
  | _, 0 => mkOrb O20
  | _, 1 => mkOrb O21
  | _, _ => mkOrb O22

@[expose] noncomputable def certs : Nat → Nat → List SpinCert
  | 0, 0 => C00.map mkCert
  | 0, 1 => C01.map mkCert
  | 0, _ => C02.map mkCert
  | 1, 0 => C10.map mkCert
  | 1, 1 => C11.map mkCert
  | 1, _ => C12.map mkCert
  | _, 0 => C20.map mkCert
  | _, 1 => C21.map mkCert
  | _, _ => C22.map mkCert

@[expose] noncomputable def tauK (j : Nat) : Bool := checkTau j (cd j)

@[expose] noncomputable def lenK (n : Nat) : Bool := (certs (n / 3) (n % 3)).length == 127

@[expose] noncomputable def orbK (n : Nat) : Bool := checkOrb (cd (n / 3)) (n % 3) (od (n / 3) (n % 3))

@[expose] noncomputable def spinK (n : Nat) : Bool :=
  checkSpinFrom (tabL (cd (n / 12)).tau) (od (n / 12) (n / 4 % 3)) (32 * (n % 4) + 1)
    (((certs (n / 12) (n / 4 % 3)).drop (32 * (n % 4))).take 32)

end CertificateChecks.KernelSL4Mod
