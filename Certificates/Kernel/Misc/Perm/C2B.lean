module

public import Certificates.Kernel.Misc.Perm.C2K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.NativeSchreierCard

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.RankThree.Native.F2

@[expose] noncomputable def bindAC (j : ℕ) : Bool :=
  allN 19 fun t => (fun k => bindK (HA.F k) (AM k) (AMI k)) (Nat.add (Nat.mul 19 j) t)

end CertificateChecks.KernelMisc.Co2K

#kc_each CertificateChecks.KernelMisc.Co2K.bindAC 0 2

namespace CertificateChecks.KernelMisc.Co2K

#kc_forall_chunks bindA_chunks (fun j => bindAC j = true) 2 CertificateChecks.KernelMisc.Co2K.bindAC 1

end CertificateChecks.KernelMisc.Co2K

end
