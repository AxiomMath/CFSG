module

public import Certificates.Kernel.J4Hub.Card
public import CFSG.Sporadic.J4.Struct.Orbit
import Certificates.Kernel.J4.Assemble
import Certificates.Kernel.J4.ChecksFix
import Certificates.Kernel.J4.ChecksPts
import Certificates.Kernel.J4.ChecksMFix
import CFSG.Certificates.Kernel.J4.KShapeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelJ4Hub

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.J4 CFSG.Certificates CFSG.Certificates.J4R
  CFSG.Sporadic.J4.Struct

noncomputable abbrev Kz : Subgroup J := Subgroup.closure {X, Y, zElt X Y T}

@[expose] def nD (i : Fin 6) : ℕ := [15180, 3400320, 32643072, 28336, 54405120, 82575360][i]

theorem dch_len : CFSG.KJ4.RUN.kd.DCH.length = 6 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem bk_eq : CFSG.KJ4.RUN.kd.BK = 501397585920 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem bd_mul (i : Fin 6) : dchBD CFSG.KJ4.RUN.kd i.val * nD i = 501397585920 := by
  fin_cases i <;> exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem bd_pos (i : Fin 6) : 0 < dchBD CFSG.KJ4.RUN.kd i.val := by
  have := bd_mul i
  rcases Nat.eq_zero_or_pos (dchBD CFSG.KJ4.RUN.kd i.val) with h | h
  · rw [h, zero_mul] at this
    exact absurd this (by norm_num)
  · exact h

theorem sum_nD : ∑ i, nD i = 173067388 := by decide

theorem prim_nD : ∀ S : Finset (Fin 6), (1 + ∑ i ∈ S, nD i) ∣ (1 + ∑ i, nD i) → S = ∅ ∨ S = Finset.univ := by
  decide

theorem nD_inj : Function.Injective nD := by decide

theorem dc_data : Nat.card Kz ≤ 501397585920 ∧ ∃ wr : ℕ → J,
    (∀ g : J, g ∈ Kz ∨ ∃ i : Fin 6, g ∈ dcSet Kz (wr i.val)) ∧
    ∀ i : Fin 6, (dcSet Kz (wr i.val)).ncard ≤ Nat.card Kz * nD i := by
  obtain ⟨-, hK, wr, -, hcov, hsz⟩ := j4Ok_dc_sound CertificateChecks.KernelBounds.J4.j4_ok
    CertificateChecks.KernelBounds.J4.fix_ok CertificateChecks.KernelBounds.J4.pts_ok
    CertificateChecks.KernelBounds.J4.mfix_ok
    CFSG.Certificates.J4KShape.wrec_len (by decide +kernel) CertificateChecks.KernelBounds.j4_hN X Y T
    (mul_eq_one_iff_inv_eq.mpr T_inv) hR_XYT
  refine ⟨bk_eq ▸ hK, wr, fun g => ?_, fun i => ?_⟩
  · have hg : g ∈ Hxyt := xyt_top ▸ Subgroup.mem_top g
    rcases hcov g hg with h | ⟨i, hi, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨⟨i, by rw [dch_len] at hi; exact hi⟩, h⟩
  · have h := hsz i.val (by rw [dch_len]; exact i.isLt)
    rw [bk_eq, ← bd_mul i, mul_comm (dchBD _ _) (nD i), ← mul_assoc] at h
    exact Nat.le_of_mul_le_mul_right h (bd_pos i)

theorem card_K_le : Nat.card Kz * (1 + ∑ i, nD i) ≤ Nat.card J := by
  rw [card_J', sum_nD]
  have := dc_data.1
  calc Nat.card Kz * (1 + 173067388) ≤ 501397585920 * (1 + 173067388) := Nat.mul_le_mul_right _ this
    _ = 86775571046077562880 := by norm_num

theorem isCoatom_K : IsCoatom Kz := by
  have : Finite J := finite_J
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨-, wr, hcov, hsz⟩ := dc_data
  exact isCoatom_of_dcSet (w := fun i => wr i.val) hcov hsz card_K_le prim_nD (by rw [sum_nD]; norm_num)

end CertificateChecks.KernelJ4Hub

end
