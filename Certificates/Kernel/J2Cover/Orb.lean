module

public import Certificates.Kernel.J2Cover.OrbData
public import Certificates.Kernel.J2Cover.AutChain
public import CFSG.Certificates.Kernel.J2OrbSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.J2Orb CFSG.Sporadic.J2.Native
open CFSG.Sporadic.Th.Native CFSG.ComponentClassification.J2Cover.Models

theorem orbOK : orbK 5 14 400 315 mA mB root PTP ALP BEP = true := by quickRfl

theorem alpha_eq : (orbitData ()).alpha =
    Array.ofFn (n := 315) (fun i => UInt32.ofNat (pg 9 511 ALP i.val)) :=
  (orbBFS_sound orbOK).1

theorem beta_eq : (orbitData ()).beta =
    Array.ofFn (n := 315) (fun i => UInt32.ofNat (pg 9 511 BEP i.val)) :=
  (orbBFS_sound orbOK).2

theorem kA : allN 315 (fun i => Nat.beq (pg 9 511 ALP i) (pg 9 (mask 9) (PA.S 0) i)) = true := by
  quickRfl

theorem kB : allN 315 (fun i => Nat.beq (pg 9 511 BEP i) (pg 9 (mask 9) (PA.S 1) i)) = true := by
  quickRfl

theorem kLtA : allN 315 (fun i => Nat.blt (pg 9 511 ALP i) 512) = true := by quickRfl

theorem kLtB : allN 315 (fun i => Nat.blt (pg 9 511 BEP i) 512) = true := by quickRfl

theorem ofFn_ap {T : Nat} {P : Nat} (hlt : ∀ i < 315, pg 9 511 T i < 512)
    (h : ∀ i < 315, pg 9 511 T i = pg 9 (mask 9) P i) :
    (Array.ofFn (n := 315) fun i =>
      ap (Array.ofFn (n := 315) fun j => UInt32.ofNat (pg 9 511 T j.val)) i.val) =
      unpack 315 9 P := by
  unfold unpack
  refine congrArg (Array.ofFn (n := 315)) (funext fun i => ?_)
  unfold ap
  rw [getElem!_pos _ i.val (by simp), Array.getElem_ofFn]
  have hx : pg 9 511 T i.val < UInt32.size := Nat.lt_of_lt_of_le (hlt i.val i.isLt) (by decide)
  rw [UInt32.toNat_ofNat_of_lt' hx, h i.val i.isLt]

theorem alphaArr_eq : alphaArr = unpack 315 9 (PA.S 0) := by
  unfold alphaArr
  rw [alpha_eq]
  exact ofFn_ap (fun i hi => Nat.le_of_ble_eq_true (allN_spec kLtA i hi))
    (fun i hi => Nat.eq_of_beq_eq_true (allN_spec kA i hi))

theorem betaArr_eq : betaArr = unpack 315 9 (PA.S 1) := by
  unfold betaArr
  rw [beta_eq]
  exact ofFn_ap (fun i hi => Nat.le_of_ble_eq_true (allN_spec kLtB i hi))
    (fun i hi => Nat.eq_of_beq_eq_true (allN_spec kB i hi))

end CertificateChecks.KernelJ2Cover

end
