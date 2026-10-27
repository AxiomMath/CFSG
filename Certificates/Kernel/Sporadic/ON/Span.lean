module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import CFSG.Certificates.Kernel.Spor.ONLin
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

open CFSG.F3.Native

meta def packVS (v : V) : Nat := v.p ||| (v.m <<< 256)

meta def spM : List Nat := CFSG.ONSchreier.Data.spanIdx.toList

meta def rcSM : List Nat :=
  (transpose 154 (rowsOf 154 CFSG.ONSchreier.Data.spanInvPayload)).toList.map packVS

end CertificateChecks.KernelSpor.ON

#knatlist CertificateChecks.KernelSpor.ON.SP CertificateChecks.KernelSpor.ON.spM
#knatlist CertificateChecks.KernelSpor.ON.RC CertificateChecks.KernelSpor.ON.rcSM

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONLin

@[expose] noncomputable def SKL : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ ih => key ONV.K p :: ih) SP

@[expose] noncomputable def spanK : Bool :=
  bAnd(Nat.beq (List.length SP) 154, bAnd(Nat.beq (List.length RC) 154,
    bAnd(allN 154 (fun t => Nat.blt (List.getD SP t 0) 245520),
    allN 154 fun k => strictB (List.getD RC k 0) fun c =>
      bAnd(canon c, Nat.beq (mv SKL c) (vmk (Nat.pow 2 k) 0)))))

theorem span_ok : spanK = true := by quickRfl

theorem strictB_val (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem SKL_eq : SKL = SP.map (key ONV.K) := by
  unfold SKL
  induction SP with
  | nil => rfl
  | cons p l ih => simp [ih]

theorem vz_unit {k : Nat} (hk : k < 154) : vz (vmk (2 ^ k) 0) = Pi.single ⟨k, hk⟩ 1 := by
  have hp : 2 ^ k < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  funext t
  unfold vz
  rw [vOf_vmk hp, CFSG.F3.Native.V.val_eq_bitVal, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases e : t = ⟨k, hk⟩
  · subst e
    simp [CFSG.F3.Native.bitVal]
  · have : ¬ k = t.val := fun h => e (Fin.ext h.symm)
    simp [CFSG.F3.Native.bitVal, this, e]

theorem spans (hc : ∀ i < 245520, canon (key ONV.K i) = true) :
    Spans 245520 (key ONV.K) fun t => List.getD SP t 0 := by
  have h := span_ok
  unfold spanK at h
  simp only [bAnd_iff, Nat.beq_eq] at h
  obtain ⟨hl1, hl2, hlt, hcol⟩ := h
  have hlt' : ∀ t < 154, List.getD SP t 0 < 245520 := fun t ht => Nat.blt_eq.mp (allN_spec hlt t ht)
  refine ⟨hlt', fun k => ?_⟩
  have hk := allN_spec hcol k.val k.isLt
  rw [strictB_val] at hk
  simp only [bAnd_iff, Nat.beq_eq] at hk
  obtain ⟨hcan, hmv⟩ := hk
  have hlen : SKL.length = 154 := by rw [SKL_eq, List.length_map, hl1]
  have hget : ∀ t < 154, SKL.getD t 0 = key ONV.K (List.getD SP t 0) := fun t ht => by
    rw [SKL_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  have hcols : ∀ t < 154, canon (SKL.getD t 0) = true := fun t ht => by
    rw [hget t ht]
    exact hc _ (hlt' t ht)
  refine ⟨vz (List.getD RC k.val 0), ?_⟩
  have hmv' : mv SKL (List.getD RC k.val 0) = vmk (2 ^ k.val) 0 := hmv
  rw [← vz_unit k.isLt, ← hmv', vz_mv hlen hcols hcan]
  funext i
  simp only [Matrix.mulVec, dotProduct, colMat, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm, hget t.val t.isLt]
  rfl

end CertificateChecks.KernelSpor.ON

end
