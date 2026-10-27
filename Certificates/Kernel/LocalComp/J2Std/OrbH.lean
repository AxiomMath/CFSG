module

public import Certificates.Kernel.LocalComp.J2Std.OrbBase
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.J2StdOrb CFSG.ComponentClassification.RankTwoClassical.J2Std

@[expose] public noncomputable def chH (c : Nat) : Bool :=
  chunkOK (K2 H0P H1P) 604800 j2StdOWHc c

@[expose] public noncomputable def chR (c : Nat) : Bool := chunkOK (K2 R1P R2P) 604800 j2A4OWRc c

@[expose] public noncomputable def chZ3 (c : Nat) : Bool := chunkOK (K1 Z3P) 604800 j2A4OW3c c

end CertificateChecks.KernelLC.J2Std

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelLC.J2Std.OH CertificateChecks.KernelLC.J2Std.chH 60
#kss_each CertificateChecks.KernelLC.J2Std.OR CertificateChecks.KernelLC.J2Std.chR 3
#kss_each CertificateChecks.KernelLC.J2Std.OZ3 CertificateChecks.KernelLC.J2Std.chZ3 17

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.J2StdOrb CFSG.ComponentClassification.RankTwoClassical.J2Std
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts)

theorem orbH : orbOK j2StdOWH 60480 keyPts2 (fun w => conjW w j2StdH0 ++ conjW w j2StdH1) =
    true :=
  orbOK_of_chunks rfl (Nat.eq_of_beq_eq_true (by quickRfl))
    (fun _ hw => keyEq2 hH0 vH0 hH1 vH1 hw) fun c hc => OH.all c hc

theorem orbR : orbOK j2A4OWR 2520 keyPts2 (fun w => conjW w j2A4R1 ++ conjW w j2A4R2) = true :=
  orbOK_of_chunks rfl (Nat.eq_of_beq_eq_true (by quickRfl))
    (fun _ hw => keyEq2 hR1 vR1 hR2 vR2 hw) fun c hc => OR.all c hc

theorem orbZ3 : orbOK j2A4OW3 16800 keyPts (conjW · j2A4Z3) = true :=
  orbOK_of_chunks rfl (Nat.eq_of_beq_eq_true (by quickRfl)) (fun _ hw => keyEq1 hZ3 vZ3 hw)
    fun c hc => OZ3.all c hc

end CertificateChecks.KernelLC.J2Std

end
