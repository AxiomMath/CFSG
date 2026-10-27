module

public import Certificates.Kernel.J4M2.C12607Checks
public import Certificates.Data.J4M2.Orbit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Br

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KC.Loop CFSG.KD.J4Q CFSG.KS.SporSch.J4B
  CertificateChecks.KernelSporSch.J4E7 CertificateChecks.KernelJ4Gam
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77

@[expose] noncomputable def vk (i : Nat) : Nat := getN 0 CFSG.Quasithin.J4M2.vecData i

@[expose] noncomputable def actK (G : Nat) (π : Nat → Nat) (i : Nat) : Bool :=
  andB (Nat.blt (π i) 77) (Nat.beq (vecJ rm (vk (π i)) G) (vk i))

@[expose] noncomputable def actAll (G : Nat) (π : Nat → Nat) : Bool := (List.range 77).all (actK G π)

theorem ac_a : actAll GA.1 (fun i => dataA.getD i 0) = true := by quickRfl
theorem ac_b : actAll GB.1 (fun i => dataB.getD i 0) = true := by quickRfl
theorem ac_z : actAll GZ.1 (fun i => dataZ.getD i 0) = true := by quickRfl

theorem cm_a : Nat.beq (mulJ c rm GA.1 ZM) (mulJ c rm ZM GA.1) = true := by quickRfl
theorem cm_b : Nat.beq (mulJ c rm GB.1 ZM) (mulJ c rm ZM GB.1) = true := by quickRfl
theorem cm_z : Nat.beq (mulJ c rm GZ.1 ZM) (mulJ c rm ZM GZ.1) = true := by quickRfl

end CertificateChecks.KernelJ4Br

end
