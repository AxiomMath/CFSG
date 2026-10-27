module

public import Certificates.Kernel.J2Cover.M22TrN
public import Certificates.Kernel.J2Cover.M22Fold
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.Monster.B.Co2 (allLt_iff)

private theorem strictB_m22 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem blt_m22 {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem testBit_xorRN (p : Nat → Nat) (j lo : Nat) :
    ∀ len, (xorRN p lo len).testBit j = xorR (fun i => (p i).testBit j) lo len
  | 0 => Nat.zero_testBit j
  | len + 1 => by
    change (Nat.xor (xorRN p lo len) (p (Nat.add lo len))).testBit j =
      Bool.xor (xorR (fun i => (p i).testBit j) lo len) ((p (Nat.add lo len)).testBit j)
    rw [← testBit_xorRN p j lo len]
    exact Nat.testBit_xor _ _ _

theorem testBit_xrN (p : Nat → Nat) (j : Nat) :
    (xrN p).testBit j = xr4725 (fun i => (p i).testBit j) := by
  have e : (fun k => (xorRN p (Nat.mul 64 k) 64).testBit j) =
      fun k => xorR (fun i => (p i).testBit j) (64 * k) 64 :=
    funext fun k => testBit_xorRN p j _ 64
  change ((xorRN (fun k => xorRN p (Nat.mul 64 k) 64) 0 73) ^^^ (xorRN p 4672 53)).testBit j =
    Bool.xor (xorR (fun k => xorR (fun i => (p i).testBit j) (64 * k) 64) 0 73)
      (xorR (fun i => (p i).testBit j) (64 * 73) 53)
  rw [Nat.testBit_xor, testBit_xorRN, testBit_xorRN, e]

theorem testBit_t7 (R x y j : Nat) (hj : j < 7) :
    (t7 R x y).testBit j = R.testBit (1024 * x + 8 * y + j) := by
  change ((R >>> ((x <<< 10) + (y <<< 3))) &&& 127).testBit j = _
  have h127 : (127 : Nat).testBit j = true := by interval_cases j <;> rfl
  have e : x * 2 ^ 10 + y * 2 ^ 3 + j = 1024 * x + 8 * y + j := by ring
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.shiftLeft_eq, Nat.shiftLeft_eq, h127,
    Bool.and_true, e]

theorem pK_lt (i a : Nat) : pK i a < 128 := by
  unfold pK
  cases Nat.blt a 128
  · exact Nat.zero_lt_succ _
  · exact Nat.and_lt_two_pow (n := 7) _ (by decide)

theorem stR_eq (R : Nat) {a d : Nat} (ha : a < 128) (hd : d < 128) (i : Nat) :
    stR R (DP a) (DI a) (DP d) i = t7 R (pK i a) (pK (iK i a) d) := by
  unfold pK iK
  rw [blt_m22 ha, blt_m22 hd]
  rfl

theorem r7_spec {x y : Nat} (hx : x < 128) (hy : y < 128) :
    (∀ j < 6, (R7P 0).testBit (1024 * x + 8 * y + j) = bitR (hRK j) x y) ∧
      (R7P 0).testBit (1024 * x + 8 * y + 6) = bitR fRK x y := by
  have hm : 128 * x + y < 16384 := by omega
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) R7B.all (128 * x + y) hm
  have e1 : (128 * x + y) / 128 = x := by omega
  have e2 : (128 * x + y) % 128 = y := by omega
  unfold fR7P fR7 at h
  rw [e1, e2] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun j hj => ?_, h6⟩
  interval_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem trBit_lane {a d : Nat} (ha : a < 128) (hd : d < 128) :
    (∀ j < 6, trBitG pK iK (hRK j) a d = (trN (R7P 0) a d).testBit j) ∧
      trBitG pK iK fRK a d = (trN (R7P 0) a d).testBit 6 := by
  refine ⟨fun j hj => ?_, ?_⟩
  · unfold trBitG trN
    rw [xor4725, testBit_xrN]
    congr 1
    funext i
    rw [stR_eq _ ha hd, testBit_t7 _ _ _ _ (by omega),
      (r7_spec (pK_lt i a) (pK_lt (iK i a) d)).1 j hj]
  · unfold trBitG trN
    rw [xor4725, testBit_xrN]
    congr 1
    funext i
    rw [stR_eq _ ha hd, testBit_t7 _ _ _ _ (by omega),
      (r7_spec (pK_lt i a) (pK_lt (iK i a) d)).2]

theorem fT7_spec {k d : Nat} (hk : k < 3) (hd : d < 128) :
    (∀ j < 6, hOK (trN (R7P 0) (k + 1) d) (k + 1) d j = true) ∧
      fOK (trN (R7P 0) (k + 1) d) (k + 1) d = true := by
  have hm : 128 * k + d < 384 := by omega
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) TPB.all (128 * k + d) hm
  have e1 : (128 * k + d) / 128 = k := by omega
  have e2 : (128 * k + d) % 128 = d := by omega
  unfold fT7P fT7 at h
  rw [e1, e2] at h
  beta_reduce at h
  rw [strictB_m22] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun j hj => ?_, h6⟩
  interval_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem kTrAB : ((allLt 6 fun j => !maskBit (bMask j) 0) && !maskBit muMask 0) = true := by
  rw [allLt_eq_allN]
  quickRfl

theorem trC : transferCheck = true := by
  rw [transferCheck_eq, mt_eq, pT_eq, iT_eq, fR_eq, hR_eq]
  have q3 : allLt 6 (fun j => allLt 3 fun k => allLt 128 fun d =>
      trBitG pK iK (hRK j) (k + 1) d ==
        ((eBit j && bitR fRK (k + 1) d) ^^ cobBitG mtK (bMask j) (k + 1) d)) = true := by
    refine allLt_iff.2 fun j hj => allLt_iff.2 fun k hk => allLt_iff.2 fun d hd => ?_
    rw [(trBit_lane (a := k + 1) (by omega) hd).1 j hj]
    exact (fT7_spec hk hd).1 j hj
  have q4 : allLt 3 (fun k => allLt 128 fun d =>
      (trBitG pK iK fRK (k + 1) d ^^ cobBitG mtK muMask (k + 1) d) == bitR fRK (k + 1) d) = true := by
    refine allLt_iff.2 fun k hk => allLt_iff.2 fun d hd => ?_
    have h := (fT7_spec hk hd).2
    rw [(trBit_lane (a := k + 1) (by omega) hd).2]
    unfold fOK at h
    revert h
    generalize (trN (R7P 0) (k + 1) d).testBit 6 = t
    generalize bitR fRK (k + 1) d = b
    generalize cobBitG mtK muMask (k + 1) d = c
    cases t <;> cases b <;> cases c <;> decide
  unfold transferCheckG
  rw [q3, q4, kTrAB]
  rfl

end CertificateChecks.KernelJ2Cover

end
