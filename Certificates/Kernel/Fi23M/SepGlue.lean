
module

public import Certificates.Kernel.Fi23M.Matrix
public import Certificates.Kernel.Fi23M.SepK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.KS.F3L CFSG.KS.Mat3 CFSG.KD.Fi23M CFSG.KD.Fi23K CFSG.KC.Fi23K
  CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

theorem LO_eq : LO = 2 ^ 64009 - 1 := CFSG.KS.Mat3.pow_sub_one_eq 64009

theorem lane_p_bit (X t : Nat) : (lane X).p.testBit t = (decide (t < 64009) && X.testBit t) := by
  change (X &&& LO).testBit t = _
  rw [LO_eq, lo_bit]

theorem lane_m_bit (X t : Nat) : (lane X).m.testBit t = X.testBit (64009 + t) := by
  change (X >>> 64009).testBit t = _
  rw [Nat.testBit_shiftRight]

theorem lane_wf {X : Nat} (hX : Canon3 64009 X) : (lane X).wf = true := by
  apply V.wf_of_bits
  intro t
  rw [lane_p_bit, lane_m_bit]
  cases h : X.testBit t
  · simp
  · rw [hX.2 t h]
    simp

theorem toMat_unlane_lane (X : Nat) : toMat 253 (unlane 253 (lane X)) = mat3 253 64009 X := by
  ext i j
  rw [toMat_apply, unlane_get _ i.isLt, V.val_eq_bitVal, blk_p, blk_m, lane_p_bit, lane_m_bit]
  have hij : 253 * i.val + j.val < 64009 := by
    have := i.isLt
    have := j.isLt
    nlinarith
  simp only [decide_eq_true j.isLt, decide_eq_true hij, Bool.true_and]
  rfl

theorem keyW_succ (f k : Nat) (hk : k ≠ 0) : keyW (f + 1) k =
    if tb G 92 k = 1 then conjW 253 matA matA (keyW f (tb G 91 k))
    else conjW 253 matB matBi (keyW f (tb G 91 k)) := by
  rw [keyW, if_neg hk]

theorem tb92_3 : tb G 92 3 = 2 := by decide +kernel
theorem tb91_3 : tb G 91 3 = 1 := by decide +kernel
theorem tb92_4 : tb G 92 4 = 1 := by decide +kernel
theorem tb91_4 : tb G 91 4 = 2 := by decide +kernel
theorem tb92_5 : tb G 92 5 = 2 := by decide +kernel
theorem tb91_5 : tb G 91 5 = 2 := by decide +kernel

theorem keyf1 (f : Nat) : keyW (f + 1) 1 = conjW 253 matA matA matD := by
  rw [keyW_succ f 1 (by decide), if_pos tb92_1, tb91_1, keyW_zero]

theorem keyf2 (f : Nat) : keyW (f + 1) 2 = conjW 253 matB matBi matD := by
  rw [keyW_succ f 2 (by decide), if_neg (by rw [tb92_2]; decide), tb91_2, keyW_zero]

theorem key3 : keyW 200 3 = conjW 253 matB matBi (conjW 253 matA matA matD) := by
  rw [keyW_succ 199 3 (by decide), if_neg (by rw [tb92_3]; decide), tb91_3, keyf1]

theorem key4 : keyW 200 4 = conjW 253 matA matA (conjW 253 matB matBi matD) := by
  rw [keyW_succ 199 4 (by decide), if_pos tb92_4, tb91_4, keyf2]

theorem key5 : keyW 200 5 = conjW 253 matB matBi (conjW 253 matB matBi matD) := by
  rw [keyW_succ 199 5 (by decide), if_neg (by rw [tb92_5]; decide), tb91_5, keyf2]

theorem conj_facts {g gi X : Array W} (hgs : g.size = 253) (hg : RowsWF (toVM g))
    (hgi : RowsWF (toVM gi)) (hgc : canonM 253 (toVM gi) = true) (hX : RowsWF (toVM X)) :
    RowsWF (toVM (conjW 253 g gi X)) ∧ canonM 253 (toVM (conjW 253 g gi X)) = true ∧
      toMatW 253 (conjW 253 g gi X) = toMatW 253 g * toMatW 253 X * toMatW 253 gi :=
  ⟨RowsWF.conjW hg hgi hX, canonM_conjW hgs hg hX hgc, toMatW_conjW hgs hg hgi hX⟩

theorem vm_eq {X : Array W} {k : Nat} (hc : canonM 253 (toVM X) = true) (hk : k < 10)
    (h : toMatW 253 X = mat3 253 64009 (RS k)) : toVM X = unlane 253 (lane (RS k)) :=
  eq_of_canonM hc (canonM_unlane 253 (lane_wf (good k hk).1)) (by
    change toMatW 253 X = _
    rw [h, toMat_unlane_lane])

theorem vm0 : toVM (keyW 200 0) = unlane 253 (lane (RS 1)) := by
  rw [keyW_zero]
  exact vm_eq canonM_matD (by norm_num) (by rw [matD_facts.2.2, mat_D])

theorem vm1 : toVM (keyW 200 1) = unlane 253 (lane (RS 3)) := by
  obtain ⟨-, hc, hm⟩ := conj_facts matA_size rowsWF_matA rowsWF_matA canonM_matA matD_facts.2.1
  rw [key1]
  exact vm_eq hc (by norm_num) (by rw [hm, toMatW_matA, matD_facts.2.2, mat_K1])

theorem vm2 : toVM (keyW 200 2) = unlane 253 (lane (RS 4)) := by
  obtain ⟨-, hc, hm⟩ := conj_facts matB_size rowsWF_matB rowsWF_matBi canonM_matBi matD_facts.2.1
  rw [key2]
  exact vm_eq hc (by norm_num) (by rw [hm, toMatW_matB, toMatW_matBi, matD_facts.2.2, mat_K2])

theorem vm3 : toVM (keyW 200 3) = unlane 253 (lane (RS 5)) := by
  obtain ⟨w1, -, m1⟩ := conj_facts matA_size rowsWF_matA rowsWF_matA canonM_matA matD_facts.2.1
  obtain ⟨-, hc, hm⟩ := conj_facts matB_size rowsWF_matB rowsWF_matBi canonM_matBi w1
  rw [key3]
  exact vm_eq hc (by norm_num) (by
    rw [hm, m1, toMatW_matA, toMatW_matB, toMatW_matBi, matD_facts.2.2, mat_K3, mat_K1])

theorem vm4 : toVM (keyW 200 4) = unlane 253 (lane (RS 6)) := by
  obtain ⟨w1, -, m1⟩ := conj_facts matB_size rowsWF_matB rowsWF_matBi canonM_matBi matD_facts.2.1
  obtain ⟨-, hc, hm⟩ := conj_facts matA_size rowsWF_matA rowsWF_matA canonM_matA w1
  rw [key4]
  exact vm_eq hc (by norm_num) (by
    rw [hm, m1, toMatW_matA, toMatW_matB, toMatW_matBi, matD_facts.2.2, mat_K4, mat_K2])

theorem vm5 : toVM (keyW 200 5) = unlane 253 (lane (RS 7)) := by
  obtain ⟨w1, -, m1⟩ := conj_facts matB_size rowsWF_matB rowsWF_matBi canonM_matBi matD_facts.2.1
  obtain ⟨-, hc, hm⟩ := conj_facts matB_size rowsWF_matB rowsWF_matBi canonM_matBi w1
  rw [key5]
  exact vm_eq hc (by norm_num) (by
    rw [hm, m1, toMatW_matB, toMatW_matBi, matD_facts.2.2, mat_K5, mat_K2])

theorem sep_mats : chainQ.map (fun r => toVM orbLit.keys[r]!) = (LsS.map (unlane 253)).toArray := by
  have hq : chainQ = #[0, 1, 2, 3, 4, 5] := rfl
  rw [hq]
  simp only [List.map_toArray, List.map_cons, List.map_nil, LsS]
  rw [keys_get (i := 0) (by norm_num), keys_get (i := 1) (by norm_num),
    keys_get (i := 2) (by norm_num), keys_get (i := 3) (by norm_num),
    keys_get (i := 4) (by norm_num), keys_get (i := 5) (by norm_num),
    vm0, vm1, vm2, vm3, vm4, vm5]

theorem sep_ok : sepOK 253 (chainQ.map fun r => toVM orbLit.keys[r]!) sepTerms (sepVec ())
    (sepK ()) (sepP ()) (sepTinv ()) sepTree = true := by
  rw [sep_mats]
  exact sepK_ok

end CertificateChecks.KernelFi23M

end
