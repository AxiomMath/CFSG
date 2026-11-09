module

public import Certificates.Kernel.J2Cover.M22Fold
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models

@[expose] noncomputable def ccTb (m x : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false
    (Nat.beq (Nat.land (nat_lit 1) (Nat.shiftRight m x)) (nat_lit 0))

@[expose] noncomputable def ccNot (a : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def ccXor (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) b (ccNot b) a

@[expose] noncomputable def ccBeq (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (ccNot b) b a

theorem testBit_eq_ccTb (m x : Nat) : m.testBit x = ccTb m x := by
  unfold ccTb Nat.testBit
  change (Nat.land 1 (Nat.shiftRight m x) != 0) = _
  generalize Nat.land 1 (Nat.shiftRight m x) = a
  cases h : Nat.beq a 0
  · have : a ≠ 0 := fun e => by rw [e] at h; exact Bool.noConfusion h
    simp [this]
  · have : a = 0 := Nat.eq_of_beq_eq_true h
    subst this
    rfl

theorem bitR_eq_ccTb (rf : Nat → Nat) (x y : Nat) : bitR rf x y = ccTb (rf x) y :=
  testBit_eq_ccTb _ _

theorem maskBit_eq_ccTb (m x : Nat) : maskBit m x = ccTb m x := testBit_eq_ccTb _ _

theorem not_eq_ccNot (a : Bool) : (!a) = ccNot a := by cases a <;> rfl

theorem xor_eq_ccXor (a b : Bool) : (a ^^ b) = ccXor a b := by cases a <;> cases b <;> rfl

theorem beq_eq_ccBeq (a b : Bool) : (a == b) = ccBeq a b := by cases a <;> cases b <;> rfl

theorem cocyC : cocycleCheck = true := by
  rw [cocycleCheck_eq, mt_eq, lm_eq, fR_eq, hR_eq]
  unfold cocycleCheckG normCocOKG treeNormOKG
  simp only [allLt_eq_allN, bitR_eq_ccTb, maskBit_eq_ccTb, not_eq_ccNot, xor_eq_ccXor,
    beq_eq_ccBeq]
  quickRfl

theorem grpC : groupCheck = true := by
  rw [groupCheck_eq, mt_eq, bt_eq, fR_eq]
  unfold groupCheckG centerOK rootCounts sqCount fourthCount
  simp only [allLt_eq_allN, countFold_eq]
  quickRfl

end CertificateChecks.KernelJ2Cover

end
