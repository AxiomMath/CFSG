module

public import Certificates.Kernel.Misc.Perm.J2Fam
public import Certificates.Kernel.Misc.Perm.J2C3B
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2Fam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CertificateChecks.KernelMisc.J2C3 (cm I X chunkK)

@[expose] noncomputable def ksK (a b t : ℕ) : Bool :=
  !(Nat.beq (cm t t) I && !(Nat.beq t I) &&
      Nat.beq (ppow 315 9 (mask 9) (pidn 315 9) (cm X t) 5) I) ||
    (Nat.beq (cm t a) (cm a t) && Nat.beq (cm t b) (cm b t))

@[expose] noncomputable def ksCzC : ℕ → Bool := chunkK 270 fun k => ksK V1 V2 (J2C3.CzP.F k)

end CertificateChecks.KernelMisc.J2Fam

#kc_each CertificateChecks.KernelMisc.J2Fam.ksCzC 0 4

namespace CertificateChecks.KernelMisc.J2Fam

open CertificateChecks.KernelMisc.J2C3 (chunkK all_of_chunks)
open CFSG.KC.Misc.Clos (allR forall_of_chunks)

#kc_forall_chunks ksCzS (fun c => ksCzC c = true) 4 CertificateChecks.KernelMisc.J2Fam.ksCzC 1

theorem ksCz_All : ∀ i < 1080, ksK V1 V2 (J2C3.CzP.F i) = true := all_of_chunks 270 4 ksCzS

end CertificateChecks.KernelMisc.J2Fam

end
