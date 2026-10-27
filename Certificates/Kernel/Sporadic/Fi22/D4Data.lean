module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.Fi22FiveD4
public import CFSG.Assembly.Defs

public section

namespace CertificateChecks.KernelSpor.Fi22D4

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Five.D4

meta def src : Array (Array Nat) := #[posA, resA g1A, resA g2A]

end CertificateChecks.KernelSpor.Fi22D4

end

set_option Elab.async false

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22D4T CertificateChecks.KernelSpor.Fi22D4.src 9
