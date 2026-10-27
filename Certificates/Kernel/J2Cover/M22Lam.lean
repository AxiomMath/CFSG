module

public import Certificates.Kernel.J2Cover.M22LamS
public import Certificates.Kernel.J2Cover.M22Fold
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.Monster.B.Co2 (allLt_iff)

theorem cBitG_eq (mt pT iT : Nat → Nat → Nat) (bt it aC : Nat → Nat) (fR : Nat → Nat) (i a : Nat) :
    cBitG mt pT iT bt it aC fR i a = (bitR fR (it (aC i)) (aC i) ^^ lamBit (pT i a) ^^
      bitR fR (it (aC i)) (bt (pT i a)) ^^ bitR fR (mt (it (aC i)) (bt (pT i a))) (aC (iT i a))) :=
  rfl

theorem cBit_lam {a i : Nat} (ha : a < 128) (hi : i < 4725) :
    cBitG mtK pK iK btK itK (fun i => pg 13 (mask 13) ACP i) fRK i a =
      (stL (LTP 0) (LTP 1) FRP ACP i (pg 7 (mask 7) (DP a) i) (pg 13 (mask 13) (DI a) i)).testBit 0 := by
  have ep : pK i a = pg 7 (mask 7) (DP a) i := by
    unfold pK
    rw [blt_true ha]
  have ei : iK i a = pg 13 (mask 13) (DI a) i := by
    unfold iK
    rw [blt_true ha]
  rw [cBitG_eq, ep, ei, stL_bit _ hi (pg7_lt _ _)]

theorem lamC22 : lambdaCheck = true := by
  rw [lambdaCheck_eq, mt_eq, pT_eq, iT_eq, bt_eq, it_eq, lookA, fR_eq]
  have q4 : allLt 128 (fun a =>
      (xorFold 4725 (fun i => cBitG mtK pK iK btK itK (fun i => pg 13 (mask 13) ACP i) fRK i a) ^^
        muBit a ^^ muBit (btK a)) == lamBit a) = true := by
    refine allLt_iff.2 fun a ha => ?_
    have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) ch10022LY.all a ha
    unfold fLYP fLY lamN at h
    rw [testBit_xrN] at h
    rw [xor4725, xr4725_congr fun i hi => cBit_lam ha hi]
    exact h
  unfold lambdaCheckG
  rw [q4]
  simp only [allLt_eq_allN]
  quickRfl

end CertificateChecks.KernelJ2Cover

end
