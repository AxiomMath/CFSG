module

public import Certificates.Kernel.LyGlue.Facts2
public import Certificates.Kernel.LyGlue.Facts4

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

theorem line_gg (hT : Ly243.trCheck = true) :
    Ly243.gg 0 * Ly243.lineG 1 = Ly243.lineG 2 * Ly243.gg 0 := by
  have e : eq22 243 8 (mask 8) (gcv hT 0).1 (lcv hT 1).1 (lcv hT 2).1 (gcv hT 0).1 =
      eq22C (gcv hT 0) (lcv hT 1) (lcv hT 2) (gcv hT 0) := by
    unfold eq22C
    rw [wC243]
  rw [gcv_val hT (by norm_num), lcv_val hT (by norm_num), lcv_val hT (by norm_num), k_line,
    eq22C_eq] at e
  have h := congrArg ev (of_decide_eq_true e.symm)
  rwa [ev_mul, ev_mul, ev_gcv hT (by norm_num), ev_lcv hT (by norm_num),
    ev_lcv hT (by norm_num)] at h

theorem gg0_not_mem (hT : Ly243.trCheck = true) : Ly243.gg 0 ∉ Ly243.Txy0 := by
  intro hm
  have h1 := Ly243.Txy0_linePerm_one hT _ hm 1
  have e : Ly243.gg 0 * Ly243.a3 1 * (Ly243.gg 0)⁻¹ = Ly243.a3 2 := by
    change Ly243.gg 0 * Ly243.lineG 1 * (Ly243.gg 0)⁻¹ = Ly243.lineG 2
    rw [line_gg hT]
    group
  have h2 : Ly243.a3 2 ∈ zpowers (Ly243.a3 1) := by
    rw [← e]
    exact h1
  exact (Ly243.lineData_a3 hT).not_mem 1 2 (by decide) h2

theorem card_Tx0_ge (hT : Ly243.trCheck = true) : 7776 ≤ Nat.card Ly243.Tx0 := by
  have hle := Ly243.Txy0_le_Tx0 hT
  set H := Ly243.Txy0.subgroupOf Ly243.Tx0
  have hH : Nat.card H = 3888 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact Glue.card_Txy0_243 hT
  have hne : H ≠ ⊤ := by
    intro htop
    have : (⟨Ly243.gg 0, Ly243.gg_mem_Tx0 hT (by norm_num)⟩ : Ly243.Tx0) ∈ H := by
      rw [htop]
      exact mem_top _
    exact gg0_not_mem hT this
  have hi1 : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have hfin : Finite ↥Ly243.Tx0 := inferInstance
  have hi0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have := Subgroup.card_mul_index H
  rw [hH] at this
  have h2 : 2 ≤ H.index := by omega
  rw [← this]
  calc 7776 = 3888 * 2 := by norm_num
    _ ≤ 3888 * H.index := Nat.mul_le_mul_left _ h2

theorem fT_val {a : Fin Ly0.deg} (ha : a ∈ OT) : (fT a : Nat) = FT a ∧ FT a < 243 := by
  have hb := k_tBlk
  simp only [CFSG.KS.PF.strictB_eqP] at hb
  have h1 := (blkOK_spec hb a a.2 ha).1
  exact ⟨by simp [fT, Nat.mod_eq_of_lt h1], h1⟩

end CertificateChecks.KernelLy

end
