module

public import Certificates.Data.Kernel.E27Orth.Defs
public import Certificates.Kernel.E27Orth.O73Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

public noncomputable section

namespace CertificateChecks.KernelE27Orth.O73

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Ord

@[expose] def o73131009_conjC (k : Nat) : Bool :=
  allN 729 (fun i => conjI mulO 19683 164 E Rp W (Nat.add (Nat.mul 729 k) i))

@[expose] def o73131009_repC (k : Nat) : Bool :=
  allN 41 (fun r => repI mulO cnO ONE 19683 81 E Rp Cm (Nat.add (Nat.mul 41 k) r))

end CertificateChecks.KernelE27Orth.O73

#kc_each CertificateChecks.KernelE27Orth.O73.o73131009_conjC 0 27
#kc_each CertificateChecks.KernelE27Orth.O73.o73131009_repC 0 4

namespace CertificateChecks.KernelE27Orth.O73

#kc_forall_chunks o73131009_conj (fun k => o73131009_conjC k = true) 27
  CertificateChecks.KernelE27Orth.O73.o73131009_conjC 1
#kc_forall_chunks o73131009_rep (fun k => o73131009_repC k = true) 4
  CertificateChecks.KernelE27Orth.O73.o73131009_repC 1

end CertificateChecks.KernelE27Orth.O73

end
