module

public import Certificates.Kernel.SporSch.Co1.OrbF2
public import Certificates.Data.Kernel.SporSch.Co1Full
public import Certificates.Data.Kernel.Co1BW
public meta import Certificates.Kernel.SporSch.Co1.GenFib
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co1.GenFib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Full

meta def FP : Array Nat := (CFSG.Sporadic.Co1Schreier.Native.fullOrb 2).pts

@[expose] def QU : Nat :=
  0xc00000200000300000d80000f800005e0000e60000ac800033c0000ee000b080007ce000953000fe9000c9c000aaa00001400047e00019a00041f0009e6000800000

@[expose] def QA : Nat := 0x229000

end CertificateChecks.KernelSporSch.Co1Full

#kss_co1fib CertificateChecks.KernelSporSch.Co1Full.FW CertificateChecks.KernelSporSch.Co1Orbs.F2.T
  CertificateChecks.KernelSporSch.Co1Orbs.F2.S CertificateChecks.KernelSporSch.Co1Full.FP 16120435 2048

#kss_co1fib CertificateChecks.KernelSporSch.Co1Full.FU CertificateChecks.KernelSporSch.Co1Orbs.F2.T
  CertificateChecks.KernelSporSch.Co1Orbs.F2.S CertificateChecks.KernelSporSch.Co1Full.FP 10876918 2048

namespace CertificateChecks.KernelSporSch.Co1Full

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb CFSG.KC.Co1B
open CertificateChecks.KernelSporSch.Co1Packed CertificateChecks.KernelSporSch.Co1Orbs

theorem kB1 : Nat.beq (mulWK (trK PA) (mulWK (Nat.xor QU (trK QU)) PA)) (Nat.xor QU (trK QU)) =
    true := by quickRfl
theorem kB2 : Nat.beq (mulWK (trK PB) (mulWK (Nat.xor QU (trK QU)) PB)) (Nat.xor QU (trK QU)) =
    true := by quickRfl
theorem kQ1 : allN 24 (fun i => Nat.beq (quadK QA QU (actK PA (Nat.shiftLeft 1 i)))
    (quadK QA QU (Nat.shiftLeft 1 i))) = true := by quickRfl
theorem kQ2 : allN 24 (fun i => Nat.beq (quadK QA QU (actK PB (Nat.shiftLeft 1 i)))
    (quadK QA QU (Nat.shiftLeft 1 i))) = true := by quickRfl
theorem kqz : Nat.beq (quadK QA QU 16663704) 0 = true := by quickRfl
theorem kqw : Nat.beq (quadK QA QU 16120435) 1 = true := by quickRfl
theorem kqu : Nat.beq (quadK QA QU 10876918) 0 = true := by quickRfl
theorem kq1 : Nat.beq (quadK QA QU 1) 0 = true := by quickRfl
theorem kq4096 : Nat.beq (quadK QA QU 4096) 1 = true := by quickRfl
theorem klow : allN 4096 (fun c => Nat.beq (quadK QA QU c) 0) = true := by quickRfl

theorem false_of {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem m0 : memK F2.T F2.S 98280 0 = false := false_of (by quickRfl)
theorem m1 : memK F2.T F2.S 98280 1 = false := false_of (by quickRfl)
theorem mu : memK F2.T F2.S 98280 10876918 = false := false_of (by quickRfl)
theorem kfw : FW.N = 552 := rfl
theorem kfu : FU.N = 552 := rfl

end CertificateChecks.KernelSporSch.Co1Full

end
