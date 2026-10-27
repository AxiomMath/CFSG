module

public import Certificates.Kernel.SuzPump.PumpSrc
public import Certificates.Kernel.SuzPump.Src
public import Certificates.Kernel.SuzPump.Pair
public import Certificates.Kernel.Sporadic.Suz.Chain2306
public import Certificates.Data.Kernel.Spor.RebuildK
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Kernel.B3S3.Gen
public meta import Certificates.Kernel.SuzPump.PumpSrc
public meta import Certificates.Kernel.SuzPump.Src
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kb3_enum CertificateChecks.KernelSuzPump.YE CertificateChecks.KernelSuzPump.yGs
  CertificateChecks.KernelSuzPump.keys 1782 11

public section

namespace CertificateChecks.KernelSuzPump

open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

@[expose] noncomputable def YY : Nat := (reb yTuple).1
@[expose] noncomputable def AA : Nat := (reb aβ).1
@[expose] noncomputable def BB : Nat := (reb bβ).1
@[expose] noncomputable def GG : Nat := (reb gβ).1

theorem yrb : (reb yTuple).2.2 = true ∧ (reb aβ).2.2 = true ∧ (reb bβ).2.2 = true ∧
    (reb gβ).2.2 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem yrb1 : (reb uβ).2.2 = true ∧ Nat.beq (reb uβ).1 (YE.G 0) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem yrb2 : (reb vβ).2.2 = true ∧ Nat.beq (reb vβ).1 (YE.G 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem yn0 : Nat.beq YE.N 360 = true ∧ Nat.beq YE.ng 2 = true := ⟨by quickRfl, by quickRfl⟩

theorem ysift : ∀ X ∈ [YE.G 0, YE.G 1, YY, AA, BB, GG],
    Nat.beq (Nat.shiftRight X (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) X t) 1782) = true ∧
    permB 1782 11 X = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 X = true := by
  intro X hX
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem ygens : ∀ k < 2,
    Nat.beq (cm 1782 11 (YE.G k) YY) (cm 1782 11 YY (YE.G k)) = true ∧
    Nat.beq (pw 1782 11 (YE.G k) 10) (pidn 1782 11) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem yab : CFSG.KC.LQT.P.anyN YE.N (fun i => Nat.beq (YE.T i) AA) = true ∧
    CFSG.KC.LQT.P.anyN YE.N (fun i => Nat.beq (YE.T i) BB) = true ∧
    Nat.beq (pw 1782 11 AA 3) (pidn 1782 11) = true ∧ (!Nat.beq AA (pidn 1782 11)) = true ∧
    Nat.beq (pw 1782 11 BB 3) (pidn 1782 11) = true ∧ (!Nat.beq BB (pidn 1782 11)) = true ∧
    Nat.beq (cm 1782 11 AA BB) (cm 1782 11 BB AA) = true ∧ (!Nat.beq BB AA) = true ∧
    (!Nat.beq BB (pw 1782 11 AA 2)) = true ∧
    permOK 1782 11 (mask 11) (1782 * 11) GG (pinvS 1782 11 (mask 11) GG) = true ∧
    Nat.beq (cm 1782 11 GG (cm 1782 11 AA (pinvS 1782 11 (mask 11) GG))) AA = true ∧
    Nat.beq (cm 1782 11 GG (cm 1782 11 BB (pinvS 1782 11 (mask 11) GG))) (pw 1782 11 BB 2) =
      true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl,
    by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelSuzPump

end
