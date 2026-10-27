module

public import Certificates.Kernel.J2Cover.M22LamS
public import Certificates.Kernel.J2Cover.K20Y
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.ComponentClassification.J2Cover.External (fusionBit)

theorem fusionBitF_eq (aC fP fI : Nat → Nat) (fR : Array Nat) (i : Nat) :
    fusionBitF aC fP fI fR i = (bitAt fR invTab[aC i]! (aC i) ^^ lamBit (fP i) ^^
      bitAt fR invTab[aC i]! betaTab[fP i]! ^^
        bitAt fR ((mulTab[invTab[aC i]!]!)[betaTab[fP i]!]!) (aC (fI i))) :=
  rfl

theorem fusP_lt {i : Nat} (hi : i < 4725) : pg 13 (mask 13) FPP i < 128 := by
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) LMB.all i hi
  unfold lamTK at h
  rw [strictB_eq', strictB_eq'] at h
  have key : ∀ c d : Bool, Bool.rec (motive := fun _ => Bool) false d c = true → c = true := by
    intro c d
    cases c <;> simp
  exact Nat.le_of_ble_eq_true (key _ _ h)

theorem fus_bit {i : Nat} (hi : i < 4725) :
    fusionBitF (fun i => pg 13 (mask 13) ACP i) (fun i => pg 13 (mask 13) FPP i)
      (fun i => pg 13 (mask 13) FIP i) fRows i =
      (stL (LTP 0) (LTP 1) FRP ACP i (pg 13 (mask 13) FPP i) (pg 13 (mask 13) FIP i)).testBit 0 := by
  have hit : ∀ a, invTab[a]! = itK a := fun a => congrFun it_eq a
  have hbt : ∀ a, betaTab[a]! = btK a := fun a => congrFun bt_eq a
  have hfr : ∀ x, fRows[x]! = fRK x := fun x => congrFun fR_eq x
  rw [fusionBitF_eq, stL_bit _ hi (fusP_lt hi)]
  simp only [hit, hbt, mt_pt, bitAt, bitR, hfr]

theorem xorPart : xorFold 4725 fusionBit = true := by
  rw [fusionBit_eq, lookA, lookP, lookI, xor4725, xr4725_congr fun i hi => fus_bit hi]
  have h := kFus
  unfold fusN at h
  rw [testBit_xrN] at h
  exact h

end CertificateChecks.KernelJ2Cover

end
