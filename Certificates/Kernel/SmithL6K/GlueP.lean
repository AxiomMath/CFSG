module

public import Certificates.Kernel.SmithL6K.Meet
public import CFSG.Certificates.Kernel.SmithL6KPSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel

theorem wMask_lt {i : Nat} (hi : i < 1395) : wMask i < 2 ^ 64 := by
  have h := wData_lt hi
  have e : wMask i = spanMask (wData[i]! % 64) (wData[i]! / 64 % 64) (wData[i]! / 4096) := rfl
  rw [e]
  exact spanMask_lt (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (by omega)

theorem inter_facts {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    wMask i &&& wMask j < 2 ^ 64 ∧ XorClosed (setM (wMask i &&& wMask j)) ∧
      (setM (wMask i &&& wMask j)).card ≤ 8 := by
  refine ⟨Nat.lt_of_le_of_lt Nat.and_le_left (wMask_lt hi), ?_, ?_⟩
  · rw [setM_and]
    exact xorClosed_inter (xorClosed_wMask (wData_lt hi)) (xorClosed_wMask (wData_lt hj))
  · rw [setM_and]
    exact (Finset.card_le_card Finset.inter_subset_left).trans (wMask_card hi).le

theorem meetCard_one_iff {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    (meetCard i j == 1) = twoB (wMask i &&& wMask j) := by
  rw [meetCard_formula hi hj]
  obtain ⟨hx, hX, h8⟩ := inter_facts hi hj
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, twoB_iff hx hX h8]
  rcases card_pow2 hX h8 with h | h | h | h <;> rw [h] <;> decide

end CertificateChecks.KernelSmithL6K
