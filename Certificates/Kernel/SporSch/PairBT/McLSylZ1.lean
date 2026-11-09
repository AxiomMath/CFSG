module

public import Certificates.Kernel.SporSch.PairBT.McLZOrb
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLBT

meta def z1C0 : Array (Array Nat) := #[#[3], #[6], #[6], #[2], #[2], #[4], #[3], #[1]]

meta def z1C1 : Array (Array Nat) := #[#[3], #[6], #[6], #[2], #[2], #[4], #[3], #[1]]

end CertificateChecks.KernelSporSch.McLBT

#kss_tree CertificateChecks.KernelSporSch.McLSylZ1.C0 CertificateChecks.KernelSporSch.McLBT.z1C0 16
#kss_tree CertificateChecks.KernelSporSch.McLSylZ1.C1 CertificateChecks.KernelSporSch.McLBT.z1C1 16

namespace CertificateChecks.KernelSporSch.McLSylZ1

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MBT CFSG.KS.SporSch.MOC CertificateChecks.KernelSporSch

@[expose] noncomputable def f0 : Nat → Bool := fun s => Nat.beq (cntZK 275 9 (mask 9) (pidn 275 9)
  2 5 McLBT.ws1 McLSylChk.Z (clsSub McLZC.clsD 2025 McLZC.RP) (s * 256) 256) (C0 s)

@[expose] noncomputable def f1 : Nat → Bool := fun s => Nat.beq (cntZK 275 9 (mask 9) (pidn 275 9)
  2 5 McLBT.ws1 McLSylChk.Zi (clsSub McLZC.clsD 2025 McLZC.RP) (s * 256) 256) (C1 s)

end CertificateChecks.KernelSporSch.McLSylZ1

#kss_slices CertificateChecks.KernelSporSch.McLSylZ1.S0
  CertificateChecks.KernelSporSch.McLSylZ1.f0 1 8
#kss_slices CertificateChecks.KernelSporSch.McLSylZ1.S1
  CertificateChecks.KernelSporSch.McLSylZ1.f1 1 8

end
