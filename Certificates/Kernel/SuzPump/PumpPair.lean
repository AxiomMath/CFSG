module

public import Certificates.Kernel.SuzPump.PumpSrc
public import Certificates.Kernel.SuzPump.Pair
public import Certificates.Kernel.Sporadic.BfsDataCmd
meta import Certificates.Kernel.SuzPump.PumpSrc
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzPump

meta def pumpGsM : Array (Array Nat) := pumpGs

meta def keysM : List Nat := [0, 1, 2, 3, 4, 8, 5, 6]

end CertificateChecks.KernelSuzPump

#kbfs_data CertificateChecks.KernelSuzPump.SPP 1782 11 CertificateChecks.KernelSuzPump.pumpGsM
  CertificateChecks.KernelSuzPump.keysM 60

public section

namespace CertificateChecks.KernelSuzPump

open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor

theorem prb1 : (reb g1β).2.2 = true ∧ Nat.beq (reb g1β).1 (SPP.G 0) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem prb2 : (reb g2β).2.2 = true ∧ Nat.beq (reb g2β).1 (SPP.G 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem pn0 : Nat.beq SPP.N 7560 = true := by quickRfl

theorem psiftG : ∀ k < 2, Nat.beq (Nat.shiftRight (SPP.G k) (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) (SPP.G k) t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 (SPP.G k) =
      true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem pgens : ∀ k < 2, permB 1782 11 (SPP.G k) = true ∧
    Nat.beq (cm 1782 11 (SPP.G k) XA) (cm 1782 11 XA (SPP.G k)) = true ∧
    Nat.beq (pw 1782 11 (SPP.G k) 5) (pidn 1782 11) = true ∧
      (!Nat.beq (SPP.G k) (pidn 1782 11)) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelSuzPump

end
