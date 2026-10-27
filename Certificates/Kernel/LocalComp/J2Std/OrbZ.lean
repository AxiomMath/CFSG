module

public import Certificates.Kernel.LocalComp.J2Std.OrbBase
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.J2StdOrb CFSG.ComponentClassification.RankTwoClassical.J2Std

@[expose] public noncomputable def chZ1 (c : Nat) : Bool := chunkOK (K1 Z1P) 604800 j2StdOW1c c

@[expose] public noncomputable def chZ2 (c : Nat) : Bool := chunkOK (K1 Z2P) 604800 j2StdOW2c c

end CertificateChecks.KernelLC.J2Std

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelLC.J2Std.OZ1 CertificateChecks.KernelLC.J2Std.chZ1 2
#kss_each CertificateChecks.KernelLC.J2Std.OZ2 CertificateChecks.KernelLC.J2Std.chZ2 12

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.J2StdOrb CFSG.ComponentClassification.RankTwoClassical.J2Std
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts)

theorem orbZ1 : orbOK j2StdOW1 2016 keyPts (conjW · j2StdZ1) = true :=
  orbOK_of_chunks rfl (Nat.eq_of_beq_eq_true (by quickRfl)) (fun _ hw => keyEq1 hZ1 vZ1 hw)
    fun c hc => OZ1.all c hc

theorem orbZ2 : orbOK j2StdOW2 12096 keyPts (conjW · j2StdZ2) = true :=
  orbOK_of_chunks rfl (Nat.eq_of_beq_eq_true (by quickRfl)) (fun _ hw => keyEq1 hZ2 vZ2 hw)
    fun c hc => OZ2.all c hc

end CertificateChecks.KernelLC.J2Std

end
