module

public import Certificates.Kernel.LocalComp.L34RC.Gen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.L34RC.Gen

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.L34RU.U CertificateChecks.KernelLC.L34RCGen.uM 6
#kmisc_packarrs CertificateChecks.KernelLC.L34RU.QP CertificateChecks.KernelLC.L34RCGen.qM 16

namespace CertificateChecks.KernelLC.L34RU

open CFSG.KLie.CT (fget)

@[expose] noncomputable def Q (i : Nat) : Nat :=
  fget (QP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 16)

end CertificateChecks.KernelLC.L34RU

end
