module

public import Certificates.Kernel.SuzPump.Src
public import Certificates.Kernel.Sporadic.Suz.Chain2306
public import Certificates.Data.Kernel.Spor.RebuildK
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Kernel.B3S3.GenSl
public meta import Certificates.Kernel.SuzPump.Src
public meta import Certificates.Kernel.B3S3.GenSl
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kb3_enum_sl CertificateChecks.KernelSuzPump.E CertificateChecks.KernelSuzPump.pairGs
  CertificateChecks.KernelSuzPump.keys 1782 11 27

public section

namespace CertificateChecks.KernelSuzPump

open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor

@[expose] noncomputable def reb (β : Array Nat) : Nat × Nat × Bool :=
  rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => β[l]!) 6

@[expose] noncomputable def XA : Nat := (reb xAβ).1

theorem rbX : (reb xAβ).2.2 = true := by quickRfl

theorem rb1 : (reb h1β).2.2 = true ∧ Nat.beq (reb h1β).1 (E.G 0) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rb2 : (reb h2β).2.2 = true ∧ Nat.beq (reb h2β).1 (E.G 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem n0 : Nat.beq E.N 405 = true ∧ Nat.beq E.ng 2 = true := ⟨by quickRfl, by quickRfl⟩

theorem pX : permB 1782 11 XA = true := by quickRfl

theorem siftG : ∀ k < 2, Nat.beq (Nat.shiftRight (E.G k) (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) (E.G k) t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 (E.G k) =
      true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem gens : ∀ k < 2, permB 1782 11 (E.G k) = true ∧
    Nat.beq (cm 1782 11 (E.G k) XA) (cm 1782 11 XA (E.G k)) = true ∧
    Nat.beq (pw 1782 11 (E.G k) 5) (pidn 1782 11) = true ∧
      (!Nat.beq (E.G k) (pidn 1782 11)) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem neg : (!Nat.beq (pw 1782 11 XA 5) (pidn 1782 11)) = true := by quickRfl

end CertificateChecks.KernelSuzPump

end
