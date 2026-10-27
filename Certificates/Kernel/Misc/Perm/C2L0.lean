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

theorem lev0_hd : levHd0 = true := by quickRfl

@[expose] noncomputable def edge0C (j : ℕ) : Bool :=
  allN 575 fun t => edge0 (Nat.add (Nat.mul 575 j) t)

end CertificateChecks.KernelMisc.Co2K

#kc_each CertificateChecks.KernelMisc.Co2K.edge0C 0 4

namespace CertificateChecks.KernelMisc.Co2K

#kc_forall_chunks edge0_chunks (fun j => edge0C j = true) 4 CertificateChecks.KernelMisc.Co2K.edge0C 1

end CertificateChecks.KernelMisc.Co2K

end
