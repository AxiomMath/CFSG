
module

public import CFSG.Sporadic.Fi23.SetupBase
public import CFSG.Certificates.Kernel.Spor.ConjIndexSound

public section

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native

theorem limb3_hi {x0 x1 x2 x3 : UInt64} (h : join x0 x1 x2 x3 >>> 253 = 0) :
    x3 >>> (253 - 192 : ℕ).toUInt64 = 0 := by
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_shiftRight, UInt64.toNat_zero]
  have e : (253 - 192 : ℕ).toUInt64.toNat % 64 = 61 := by decide
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_shiftRight, Nat.zero_testBit]
  by_cases ht : 61 + t < 64
  · have h' := congrArg (fun y => y.testBit t) h
    simp only [Nat.testBit_shiftRight, Nat.zero_testBit] at h'
    rw [testBit_join] at h'
    have e1 : (253 + t) / 64 = 3 := by omega
    have e2 : (253 + t) % 64 = 61 + t := by omega
    rw [e1, e2] at h'
    simpa [limb] using h'
  · exact testBit_toNat_ge x3 (by omega)

theorem W.canon_of_V {a : W}
    (h : (a.toV.wf && a.toV.p >>> 253 == 0 && a.toV.m >>> 253 == 0) = true) :
    a.canon 253 = true := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hw, hp⟩, hm⟩ := h
  have hw' : join (a.p0 &&& a.m0) (a.p1 &&& a.m1) (a.p2 &&& a.m2) (a.p3 &&& a.m3) =
      join 0 0 0 0 := by
    rw [← join_and, join_zero]
    unfold V.wf W.toV at hw
    simpa using hw
  obtain ⟨e0, e1, e2, e3⟩ := join_inj hw'
  unfold W.canon W.wf
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, limb3_hi hp⟩, limb3_hi hm⟩

theorem canonW_of_canonM {X : Array W} (h : canonM 253 (toVM X) = true) : canonW 253 X = true := by
  obtain ⟨hs, hc⟩ := canonM_spec h
  unfold canonW
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by rwa [toVM_size] at hs, fun i hi => ?_⟩
  have := hc i (by rw [toVM_size]; exact hi)
  rw [toVM_getElem!, getElem!_pos X i hi] at this
  exact W.canon_of_V this

theorem canonM_rowsOf (s : String) : canonM 253 (CFSG.F3.Native.rowsOf 253 s) = true := by
  unfold canonM
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true']
  refine ⟨by unfold CFSG.F3.Native.rowsOf; simp, fun v hv => ?_⟩
  unfold CFSG.F3.Native.rowsOf at hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  rw [Array.getElem_ofFn]
  obtain ⟨h1, h2⟩ := V.ofFn_lt 253
    (fun j => ((decodeEntries s).toArray[i * 253 + j]?.getD 0))
  simp only [V.wf_ofFn, Bool.true_and, Bool.and_eq_true]
  exact ⟨shiftRight_beq_zero h1, shiftRight_beq_zero h2⟩

theorem canonW_matA : canonW 253 matA = true := by
  apply canonW_of_canonM
  rw [toVM_matA]
  exact canonM_rowsOf _

theorem canonW_matB : canonW 253 matB = true := by
  apply canonW_of_canonM
  rw [toVM_matB]
  exact canonM_rowsOf _

theorem canonW_idW' : canonW 253 (idW 253) = true := by
  apply canonW_of_canonM
  rw [toVM_idW (by norm_num)]
  exact canonM_idM 253

theorem canonM_mulW {X Y : Array W} (hXs : X.size = 253) (hX : RowsWF (toVM X))
    (hY : canonM 253 (toVM Y) = true) : canonM 253 (toVM (mulW 253 X Y)) = true := by
  rw [toVM_mulW]
  exact canonM_mul (by rw [toVM_size, hXs]) hX hY

theorem canonM_powW {M : Array W} (hM : RowsWF (toVM M)) (hc : canonM 253 (toVM M) = true) :
    ∀ e, canonM 253 (toVM (powW 253 M e)) = true
  | 0 => by rw [powW, toVM_idW (by norm_num)]; exact canonM_idM 253
  | e + 1 => by
    rw [powW]
    exact canonM_mulW (powW_size M e) (RowsWF.powW hM e) hc

theorem canonM_matA : canonM 253 (toVM matA) = true := by
  rw [toVM_matA]; exact canonM_rowsOf _

theorem canonM_matB : canonM 253 (toVM matB) = true := by
  rw [toVM_matB]; exact canonM_rowsOf _

theorem canonM_prodW_aux (word : List ℕ) (hw : ∀ x ∈ word, x < 2) (M : Array W)
    (hMs : M.size = 253) (hM : RowsWF (toVM M)) (hc : canonM 253 (toVM M) = true) :
    canonM 253 (toVM (word.foldl (fun M x => mulW 253 M #[matA, matB][x]!) M)) = true := by
  induction word generalizing M with
  | nil => exact hc
  | cons x w ih =>
    have hx := hw x List.mem_cons_self
    obtain ⟨-, h2, -⟩ := gens_facts hx
    have hcx : canonM 253 (toVM #[matA, matB][x]!) = true := by
      obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
      · exact canonM_matA
      · exact canonM_matB
    rw [List.foldl_cons]
    exact ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ (by rw [mulW_size, hMs])
      (RowsWF.mulW hM h2) (canonM_mulW hMs hM hcx)

theorem canonM_prodW (word : List ℕ) (hw : ∀ x ∈ word, x < 2) :
    canonM 253 (toVM (prodW 253 #[matA, matB] word)) = true := by
  unfold prodW
  refine canonM_prodW_aux word hw _ idW_size rowsWF_idW ?_
  rw [toVM_idW (by norm_num)]
  exact canonM_idM 253

theorem canonW_matD : canonW 253 matD = true := by
  apply canonW_of_canonM
  unfold matD
  exact canonM_powW (prodW_facts dWord dWord_lt).2.1 (canonM_prodW dWord dWord_lt) 7

theorem eqW_of_toMatW {X Y : Array W} (hXs : X.size = 253) (hX : canonW 253 X = true)
    (hY : canonW 253 Y = true) (h : toMatW 253 X = toMatW 253 Y) : eqW 253 X Y = true := by
  have e := toVM_inj (eq_of_canonM (canonM_of_canonW (by norm_num) (by norm_num) hX)
    (canonM_of_canonW (by norm_num) (by norm_num) hY) h)
  subst e
  unfold eqW
  simp [hXs]

theorem eqW_false_of_toMatW {X Y : Array W} (h : toMatW 253 X ≠ toMatW 253 Y) :
    eqW 253 X Y = false := by
  cases hb : eqW 253 X Y
  · rfl
  · exact absurd (toMatW_eq_of_eqW hb) h

end CertificateChecks.KernelFi23M

end
