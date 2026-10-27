module

public import Certificates.Kernel.OmegaEight.Dict3851
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bits
public import Mathlib

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelO8.Dict

open CFSG.KLie.CT CFSG.KC.O8D CFSG.EvenSmallLie.OmegaEight.NSplit
  CFSG.EvenSmallLie.OmegaEight.Stage1 CertificateChecks.KernelO8

@[expose] noncomputable def Qp : Nat := 10837449240524681216
@[expose] noncomputable def Qm : Nat := 11067126980204625904

theorem kapP : ∀ x < 128, kapCode .plus x = kcK 0 x := by decide +kernel
theorem kapM : ∀ x < 128, kapCode .minus x = kcK 36 x := by decide +kernel
theorem invP : ∀ e < 128, kapInv .plus e = kiK 0 e := by decide +kernel
theorem invM : ∀ e < 128, kapInv .minus e = kiK 36 e := by decide +kernel
theorem qfP : ∀ v < 64, qfB .plus v = bit Qp v := by decide +kernel
theorem qfM : ∀ v < 64, qfB .minus v = bit Qm v := by decide +kernel

theorem kAP : allN 128 (kapAt 0) = true := by quickRfl
theorem kAM : allN 128 (kapAt 36) = true := by quickRfl
theorem kDA : allN 512 (movAt actK) = true := by quickRfl
theorem kEP : allN 64 (orbAt actK 0 Qp 64) = true := by quickRfl
theorem kEM : allN 64 (orbAt actK 36 Qm 75) = true := by quickRfl

theorem kBP0 : blk 0 (fun i => allN 64 (phiAt actK ginvK 0 Qp i)) = true := by quickRfl
theorem kBP1 : blk 1 (fun i => allN 64 (phiAt actK ginvK 0 Qp i)) = true := by quickRfl
theorem kBP2 : blk 2 (fun i => allN 64 (phiAt actK ginvK 0 Qp i)) = true := by quickRfl
theorem kBP3 : blk 3 (fun i => allN 64 (phiAt actK ginvK 0 Qp i)) = true := by quickRfl
theorem kBP4 : blk 4 (fun i => allN 64 (phiAt actK ginvK 0 Qp i)) = true := by quickRfl
theorem kBP5 : blk 5 (fun i => allN 64 (phiAt actK ginvK 0 Qp i)) = true := by quickRfl
theorem kBP6 : blk 6 (fun i => allN 64 (phiAt actK ginvK 0 Qp i)) = true := by quickRfl
theorem kBP7 : blk 7 (fun i => allN 64 (phiAt actK ginvK 0 Qp i)) = true := by quickRfl

theorem kBM0 : blk 0 (fun i => allN 64 (phiAt actK ginvK 36 Qm i)) = true := by quickRfl
theorem kBM1 : blk 1 (fun i => allN 64 (phiAt actK ginvK 36 Qm i)) = true := by quickRfl
theorem kBM2 : blk 2 (fun i => allN 64 (phiAt actK ginvK 36 Qm i)) = true := by quickRfl
theorem kBM3 : blk 3 (fun i => allN 64 (phiAt actK ginvK 36 Qm i)) = true := by quickRfl
theorem kBM4 : blk 4 (fun i => allN 64 (phiAt actK ginvK 36 Qm i)) = true := by quickRfl
theorem kBM5 : blk 5 (fun i => allN 64 (phiAt actK ginvK 36 Qm i)) = true := by quickRfl
theorem kBM6 : blk 6 (fun i => allN 64 (phiAt actK ginvK 36 Qm i)) = true := by quickRfl
theorem kBM7 : blk 7 (fun i => allN 64 (phiAt actK ginvK 36 Qm i)) = true := by quickRfl

theorem kCP0 : blk 0 (fun i => allN 128 (actAt actK 0 i)) = true := by quickRfl
theorem kCP1 : blk 1 (fun i => allN 128 (actAt actK 0 i)) = true := by quickRfl
theorem kCP2 : blk 2 (fun i => allN 128 (actAt actK 0 i)) = true := by quickRfl
theorem kCP3 : blk 3 (fun i => allN 128 (actAt actK 0 i)) = true := by quickRfl
theorem kCP4 : blk 4 (fun i => allN 128 (actAt actK 0 i)) = true := by quickRfl
theorem kCP5 : blk 5 (fun i => allN 128 (actAt actK 0 i)) = true := by quickRfl
theorem kCP6 : blk 6 (fun i => allN 128 (actAt actK 0 i)) = true := by quickRfl
theorem kCP7 : blk 7 (fun i => allN 128 (actAt actK 0 i)) = true := by quickRfl

theorem kCM0 : blk 0 (fun i => allN 128 (actAt actK 36 i)) = true := by quickRfl
theorem kCM1 : blk 1 (fun i => allN 128 (actAt actK 36 i)) = true := by quickRfl
theorem kCM2 : blk 2 (fun i => allN 128 (actAt actK 36 i)) = true := by quickRfl
theorem kCM3 : blk 3 (fun i => allN 128 (actAt actK 36 i)) = true := by quickRfl
theorem kCM4 : blk 4 (fun i => allN 128 (actAt actK 36 i)) = true := by quickRfl
theorem kCM5 : blk 5 (fun i => allN 128 (actAt actK 36 i)) = true := by quickRfl
theorem kCM6 : blk 6 (fun i => allN 128 (actAt actK 36 i)) = true := by quickRfl
theorem kCM7 : blk 7 (fun i => allN 128 (actAt actK 36 i)) = true := by quickRfl

theorem of_blk8 {f : Nat → Bool} (b0 : blk 0 f = true) (b1 : blk 1 f = true) (b2 : blk 2 f = true)
    (b3 : blk 3 f = true) (b4 : blk 4 f = true) (b5 : blk 5 f = true) (b6 : blk 6 f = true)
    (b7 : blk 7 f = true) : ∀ i < 512, f i = true :=
  of_blk fun k hk => by
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
    exacts [b0, b1, b2, b3, b4, b5, b6, b7, absurd hk (by omega)]

theorem hyp_plus : Hyp .plus 0 Qp 64 where
  hK := kapP
  hI := invP
  hQ := qfP
  ht := rfl
  kA := (allN_true _ _).1 kAP
  kB := fun i hi => (allN_true _ _).1 (of_blk8 kBP0 kBP1 kBP2 kBP3 kBP4 kBP5 kBP6 kBP7 i hi)
  kC := fun i hi => (allN_true _ _).1 (of_blk8 kCP0 kCP1 kCP2 kCP3 kCP4 kCP5 kCP6 kCP7 i hi)
  kD := (allN_true _ _).1 kDA
  kE := (allN_true _ _).1 kEP

theorem hyp_minus : Hyp .minus 36 Qm 75 where
  hK := kapM
  hI := invM
  hQ := qfM
  ht := rfl
  kA := (allN_true _ _).1 kAM
  kB := fun i hi => (allN_true _ _).1 (of_blk8 kBM0 kBM1 kBM2 kBM3 kBM4 kBM5 kBM6 kBM7 i hi)
  kC := fun i hi => (allN_true _ _).1 (of_blk8 kCM0 kCM1 kCM2 kCM3 kCM4 kCM5 kCM6 kCM7 i hi)
  kD := (allN_true _ _).1 kDA
  kE := (allN_true _ _).1 kEM

theorem cert3851 : dictCheck .plus = true ∧ dictCheck .minus = true :=
  ⟨dict_sound hyp_plus, dict_sound hyp_minus⟩

end CertificateChecks.KernelO8.Dict

end
