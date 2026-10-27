module

public import Certificates.Data.Kernel.E27Orth.Defs
public import Certificates.Kernel.E27Orth.O73Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

@[expose] public noncomputable section

namespace CertificateChecks.KernelE27Orth.O73

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Ord

theorem o73131009_consts : constsOK 3 6 42 7 3 L H CM RM ONE LV HV = true := by decide +kernel

theorem o73131009_base : baseI cnO ONE 3 G = true := by decide +kernel

@[expose] def o73131009_treeC (k : Nat) : Bool :=
  allN 729 (fun i => treeI mulO cnO ONE 3 G E Tr (Nat.add (Nat.mul 729 k) i))

@[expose] def o73131009_keyC (k : Nat) : Bool :=
  allN 729 (fun i => keyI 19683 E Ss (Nat.add (Nat.mul 729 k) i))

end CertificateChecks.KernelE27Orth.O73

#kc_each CertificateChecks.KernelE27Orth.O73.o73131009_treeC 0 27
#kc_each CertificateChecks.KernelE27Orth.O73.o73131009_keyC 0 27

namespace CertificateChecks.KernelE27Orth.O73

#kc_forall_chunks o73131009_tree (fun k => o73131009_treeC k = true) 27
  CertificateChecks.KernelE27Orth.O73.o73131009_treeC 1
#kc_forall_chunks o73131009_key (fun k => o73131009_keyC k = true) 27
  CertificateChecks.KernelE27Orth.O73.o73131009_keyC 1

end CertificateChecks.KernelE27Orth.O73

end
