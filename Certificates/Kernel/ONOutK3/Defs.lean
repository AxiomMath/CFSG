module

public import Certificates.Data.Kernel.ONOutK3.Check
public import Certificates.Kernel.ONOutK3.Data
public import Certificates.Kernel.Sporadic.ON3.Defs

public section

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3

@[expose] noncomputable def UL (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), nat_lit 1, nIf(Nat.beq l (nat_lit 1), nat_lit 17, nat_lit 14))

@[expose] noncomputable def UW (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), nat_lit 0,
    nIf(Nat.beq l (nat_lit 1), nat_lit 5996111193, nat_lit 174692968))

@[expose] noncomputable def TC (s : Nat) : Nat :=
  rget ONK3C (nat_lit 6) (nat_lit 63) (nat_lit 10) (nat_lit 1023) s

@[expose] noncomputable def FK : Nat := ONK3K (nat_lit 0)

@[expose] noncomputable def nsl (s : Nat) : Bool :=
  sliceOK CertificateChecks.KernelSpor.ON3.mG ONK3N UL UW FK TC s

@[expose] noncomputable def ssl (s : Nat) : Bool := sortSl ONK3N ONK3S s

end CertificateChecks.KernelSpor.ONK3

end
