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

@[expose] noncomputable def ptailC (j : ℕ) : Bool :=
  allN 575 fun t => ptBody (Nat.add (Nat.mul 575 j) t)

end CertificateChecks.KernelMisc.Co2K

#kc_each CertificateChecks.KernelMisc.Co2K.ptailC 0 4

namespace CertificateChecks.KernelMisc.Co2K

#kc_forall_chunks ptail_chunks (fun j => ptailC j = true) 4 CertificateChecks.KernelMisc.Co2K.ptailC 1

end CertificateChecks.KernelMisc.Co2K

end
