module

public import Certificates.Data.Kernel.ONOutK3.F
public import Certificates.Kernel.ONOutK3.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3

@[expose] noncomputable def FL : Nat := ONK3F (nat_lit 0)

@[expose] noncomputable def fchk (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 0), fAll CertificateChecks.KernelSpor.ON3.mG FL FK,
  bIf(Nat.beq c (nat_lit 1), fFixK CertificateChecks.KernelSpor.ON3.mG UL UW,
  bIf(Nat.beq c (nat_lit 2), fCommK CertificateChecks.KernelSpor.ON3.mG,
    Nat.beq (sumBlk (nat_lit 0) TC (nat_lit 315)) (nat_lit 1344))))

end CertificateChecks.KernelSpor.ONK3

#kon_slices CertificateChecks.KernelSpor.ONK3.fchk 0 4

end
