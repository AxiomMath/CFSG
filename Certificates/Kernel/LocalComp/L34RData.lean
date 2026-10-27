module

public import Certificates.Kernel.LocalComp.L34Gen
public import Certificates.Data.Kernel.L34K
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.L34Gen

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.L34R.TP CertificateChecks.KernelLC.L34Gen.rT 252
#kmisc_packarrs CertificateChecks.KernelLC.L34R.EP CertificateChecks.KernelLC.L34Gen.rE 108
#kmisc_packarrs CertificateChecks.KernelLC.L34R.SP CertificateChecks.KernelLC.L34Gen.rS 18
#kmisc_packarrs CertificateChecks.KernelLC.L34R.SIP CertificateChecks.KernelLC.L34Gen.rSI 18
#kmisc_packarrs CertificateChecks.KernelLC.L34R.C CertificateChecks.KernelLC.L34Gen.rC 32
#kmisc_packarrs CertificateChecks.KernelLC.L34R.G CertificateChecks.KernelLC.L34Gen.gP 252

namespace CertificateChecks.KernelLC.L34R

open CFSG.KLie.CT (fget)

@[expose] noncomputable def T (i : Nat) : Nat :=
  fget (TP (Nat.shiftRight i (nat_lit 3))) (Nat.land i (nat_lit 7)) (nat_lit 252)

@[expose] noncomputable def E (i : Nat) : Nat :=
  fget (EP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 108)

@[expose] noncomputable def S (i : Nat) : Nat :=
  fget (SP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 18)

@[expose] noncomputable def SI (i : Nat) : Nat :=
  fget (SIP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 18)

end CertificateChecks.KernelLC.L34R

end
