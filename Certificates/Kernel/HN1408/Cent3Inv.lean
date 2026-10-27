module

public import Certificates.Kernel.HN1408.Cent3Base
public import Certificates.Kernel.HN1408.Cent3Rows

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem bAnd_true {a b : Bool} (ha : a = true) (hb : b = true) : bAnd(a, b) = true := by
  rw [ha]
  exact hb

theorem bIf_ne_zero {k : Nat} (h : bIf(Nat.beq k 0, false, true) = true) : k ≠ 0 := by
  rintro rfl
  exact absurd h (by decide)

theorem bIf_of_ne_zero {k : Nat} (h : k ≠ 0) : bIf(Nat.beq k 0, false, true) = true := by
  have e : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
  rw [e]

theorem ev_zero {p : Nat} (hp : p < 1408) : ev 0 p = p := by
  rw [← el_pt (k := 0) (by norm_num) hp, el_zero]
  rfl

theorem sq_pt {k p : Nat} (hk : k < 1440) (hp : p < 1408) :
    ((el k * el k) ⟨p, hp⟩).val = ev k (ev k p) := by
  rw [Equiv.Perm.mul_apply, el_apply hk hp, el_pt hk (ev_lt hk hp)]

variable (hC : Nat.card cC = 1440)
include hC

theorem invK_iff {k : Nat} (hk : k < 1440) : invK k = true ↔ el k * el k = 1 ∧ el k ≠ 1 := by
  constructor
  · intro h
    unfold invK at h
    obtain ⟨h1, h2⟩ := mkA h
    obtain ⟨b0, b1⟩ := base2_parts h2
    refine ⟨?_, fun e => bIf_ne_zero h1 (el_inj hk (by norm_num) (e.trans el_zero.symm))⟩
    rw [← el_zero]
    refine eq_el hC (mul_mem (el_mem hk) (el_mem hk)) (by norm_num) ?_ ?_
    · rw [sq_pt hk, ev_zero (by norm_num)]
      exact Nat.eq_of_beq_eq_true b0
    · rw [sq_pt hk, ev_zero (by norm_num)]
      exact Nat.eq_of_beq_eq_true b1
  · rintro ⟨h2, h1⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact h1 el_zero
    have hp : ∀ p (hp : p < 1408), ev k (ev k p) = p := fun p hp => by
      rw [← sq_pt hk hp, h2]
      rfl
    unfold invK
    have e0 := hp 0 (by norm_num)
    have e1 := hp 1 (by norm_num)
    refine bAnd_true (bIf_of_ne_zero hk0) (bAnd_true ?_ ?_)
    · simp only [e0, Nat.beq_refl]
    · simp only [e1, Nat.beq_refl]

theorem row_zero {k : Nat} (hk : k < 1440) (h0 : R k = 0) : ¬ (el k * el k = 1 ∧ el k ≠ 1) := by
  intro hi
  have h := allN_spec ch441603_rows k hk
  unfold rowK at h
  simp only [strictB_app] at h
  rw [h0, (invK_iff hC hk).2 hi] at h
  exact Bool.false_ne_true h

theorem row_conj {k : Nat} (hk : k < 1440) (h0 : R k ≠ 0) :
    (R k - 1) % 8 < 6 ∧ ∃ c' < 1440, el c' * el (RK ((R k - 1) % 8)) = el k * el c' := by
  have h := allN_spec ch441603_rows k hk
  unfold rowK at h
  have e0 : Nat.beq (R k) 0 = false := Bool.eq_false_iff.2 fun h' => h0 (Nat.eq_of_beq_eq_true h')
  simp only [strictB_app] at h
  rw [e0] at h
  obtain ⟨-, h⟩ := mkA h
  obtain ⟨hc, h⟩ := mkA h
  obtain ⟨hc', h⟩ := mkA h
  obtain ⟨b0, b1⟩ := base2_parts h
  have hc6 : (R k - 1) % 8 < 6 := Nat.blt_eq.mp hc
  have hc1 : (R k - 1) / 8 < 1440 := Nat.blt_eq.mp hc'
  refine ⟨hc6, _, hc1, ?_⟩
  have hr := (allN_spec ch441603_rep _ (by omega : (R k - 1) % 8 < 6))
  unfold repK at hr
  simp only [strictB_app] at hr
  have hrk : RK ((R k - 1) % 8) < 1440 := Nat.blt_eq.mp (mkA hr).1
  refine eq_of_base hC (mul_mem (el_mem hc1) (el_mem hrk)) (mul_mem (el_mem hk) (el_mem hc1))
    (Fin.ext ?_) (Fin.ext ?_)
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, el_apply hrk (by norm_num),
      el_pt hc1 (ev_lt hrk (by norm_num)), el_apply hc1 (by norm_num), el_pt hk (ev_lt hc1 (by norm_num))]
    exact Nat.eq_of_beq_eq_true b0
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, el_apply hrk (by norm_num),
      el_pt hc1 (ev_lt hrk (by norm_num)), el_apply hc1 (by norm_num), el_pt hk (ev_lt hc1 (by norm_num))]
    exact Nat.eq_of_beq_eq_true b1

end CFSG.KD.HN1408.Cent3

end
