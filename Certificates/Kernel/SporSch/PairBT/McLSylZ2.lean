module

public import Certificates.Kernel.SporSch.PairBT.McLZOrb
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLBT

meta def z2C0 : Array (Array Nat) := #[#[1], #[0], #[0], #[1], #[0], #[0], #[0], #[0]]

meta def z2C1 : Array (Array Nat) := #[#[0], #[0], #[0], #[0], #[0], #[0], #[0], #[0]]

end CertificateChecks.KernelSporSch.McLBT

#kss_tree CertificateChecks.KernelSporSch.McLSylZ2.C0 CertificateChecks.KernelSporSch.McLBT.z2C0 16
#kss_tree CertificateChecks.KernelSporSch.McLSylZ2.C1 CertificateChecks.KernelSporSch.McLBT.z2C1 16

namespace CertificateChecks.KernelSporSch.McLSylZ2

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MBT CFSG.KS.SporSch.MOC CertificateChecks.KernelSporSch

@[expose] noncomputable def f0 : Nat → Bool := fun s => Nat.beq (cntZK 275 9 (mask 9) (pidn 275 9)
  2 5 McLBT.ws2 McLSylChk.Z (clsSub McLZC.clsD 2025 McLZC.RP) (s * 256) 256) (C0 s)

@[expose] noncomputable def f1 : Nat → Bool := fun s => Nat.beq (cntZK 275 9 (mask 9) (pidn 275 9)
  2 5 McLBT.ws2 McLSylChk.Zi (clsSub McLZC.clsD 2025 McLZC.RP) (s * 256) 256) (C1 s)

end CertificateChecks.KernelSporSch.McLSylZ2

#kss_slices CertificateChecks.KernelSporSch.McLSylZ2.S0
  CertificateChecks.KernelSporSch.McLSylZ2.f0 1 8
#kss_slices CertificateChecks.KernelSporSch.McLSylZ2.S1
  CertificateChecks.KernelSporSch.McLSylZ2.f1 1 8

end
