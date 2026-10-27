
module

import Certificates.Kernel.Fi23Tw.Rep0
import Certificates.Kernel.Fi23Tw.Rep1
public import CFSG.Certificates.Kernel.Fi23Tw.Sound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeCBase
public import Certificates.Kernel.Fi23Cls.Glue
public import Certificates.Kernel.Fi23Tw.ChkDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Tw

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K
  CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KC.Fi23Tw CFSG.KD.Fi23Tw CFSG.KD.Fi23Cls
  CertificateChecks.KernelFi23Q CertificateChecks.KernelFi23Cls
  CFSG.HardMathSupport.Dickson.I271.TabFi23 CFSG.KS.Raw.Orb
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def allR : List (List ℕ) :=
  R0 ++ R1 ++ R2 ++ R3 ++ R4 ++ R5 ++ R6 ++ R7 ++ R8 ++ R9 ++ R10 ++ R11

theorem covU_append (R R' : List (List ℕ)) (acc : ℕ) :
    covU G CFSG.KD.Fi23Tw.w2 (R ++ R') acc =
      covU G CFSG.KD.Fi23Tw.w2 R' (covU G CFSG.KD.Fi23Tw.w2 R acc) := by
  induction R generalizing acc with
  | nil => rfl
  | cons e R ih =>
    change strictN _ (covU G CFSG.KD.Fi23Tw.w2 (R ++ R')) = covU G CFSG.KD.Fi23Tw.w2 R'
      (strictN _ (covU G CFSG.KD.Fi23Tw.w2 R))
    rw [strictN_eq, strictN_eq, ih]

theorem covAll_eq : covAll = covU G CFSG.KD.Fi23Tw.w2 allR 0 := by
  unfold covAll allR
  simp only [covU_append]

theorem cover (c : ℕ) (hc : c < 31671) : ∃ e ∈ allR, c = e.getD 0 0 ∨
    c = wv G CFSG.KD.Fi23Tw.w2 (e.getD 0 0) ∨
      c = wv G CFSG.KD.Fi23Tw.w2 (wv G CFSG.KD.Fi23Tw.w2 (e.getD 0 0)) := by
  have h := Nat.eq_of_beq_eq_true (ch17340cov_ok : cov = true)
  have hb : (covU G CFSG.KD.Fi23Tw.w2 allR 0).testBit c = true := by
    rw [← covAll_eq, h]
    have key : ∀ n k : ℕ, k < n → ((1 <<< n) - 1).testBit k = true := fun n k h => by
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true h
    exact key 31671 c hc
  rcases covU_testBit c allR 0 hb with h1 | h1
  · rw [Nat.zero_testBit] at h1
    cases h1
  · exact h1

theorem rep_all : ∀ e ∈ allR, repK G CFSG.KD.Fi23Tw.w2 TG e = true := by
  intro e he
  simp only [allR, List.mem_append] at he
  rcases he with (((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · exact repAll_spec ch17340rep0_ok e h
  · exact repAll_spec ch17340rep1_ok e h
  · exact repAll_spec ch17340rep2_ok e h
  · exact repAll_spec ch17340rep3_ok e h
  · exact repAll_spec ch17340rep4_ok e h
  · exact repAll_spec ch17340rep5_ok e h
  · exact repAll_spec ch17340rep6_ok e h
  · exact repAll_spec ch17340rep7_ok e h
  · exact repAll_spec ch17340rep8_ok e h
  · exact repAll_spec ch17340rep9_ok e h
  · exact repAll_spec ch17340rep10_ok e h
  · exact repAll_spec ch17340rep11_ok e h

theorem w2_tw : CFSG.KD.Fi23Q.t3R 2 = CFSG.KD.Fi23Tw.w2 := by decide

theorem x_acts (y : Fin 31671) : wv G CFSG.KD.Fi23Tw.w2 y.val = (t3 2 • y).val := by
  rw [act_t3 (c := 2) (by norm_num) w2_tw y.val y.2, idx_of_lt _ y.2]
  rfl

theorem comm_x {a r : Fin 31671} (ha : t3 2 • a = a) :
    (ePt (t3 2 • r) * ePt a = ePt a * ePt (t3 2 • r) ↔ ePt r * ePt a = ePt a * ePt r) := by
  have hc := e_comm_of_fix (e := ePt) (x := t3 2) ePt_smul ha
  have hx : ePt a = t3 2 * ePt a * (t3 2)⁻¹ := by
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [ePt_smul]
  conv_lhs => rw [hx]
  exact twin_conj_comm_iff (t3 2) (ePt r) (ePt a)

end CertificateChecks.KernelFi23Tw

end
