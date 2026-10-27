
module

public import Certificates.Kernel.Fi23Q.WordGlue
public import CFSG.Certificates.Kernel.Fi23Q.TabSound
import Certificates.Kernel.Fi23Q.G0
import Certificates.Kernel.Fi23Q.G1
import Certificates.Kernel.Fi23Q.G2
import Certificates.Kernel.Fi23Q.C0
import Certificates.Kernel.Fi23Q.C1

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Q

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KD.Fi23K
  CFSG.KD.Fi23Q CFSG.Perm
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (qG)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native (qWords)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem cI_lt {k : ℕ} (hk : 3 ≤ k) : cI k < k := by
  unfold cI
  split_ifs <;> omega

theorem cJ_lt (k : ℕ) : cJ k < 3 := by
  unfold cJ
  split_ifs <;> omega

noncomputable def aE (k : ℕ) : CFSG.Sporadic.Fi23.J :=
  if k < 3 then qG k else if h : 3 ≤ k ∧ k < 13 then
    have := cI_lt h.1
    (aE (cI k))⁻¹ * (qG (cJ k))⁻¹ * aE (cI k) * qG (cJ k)
  else 1
termination_by k

theorem aE_lt3 {k : ℕ} (hk : k < 3) : aE k = qG k := by
  rw [aE, if_pos hk]

theorem aE_comm {k : ℕ} (h1 : 3 ≤ k) (h2 : k < 13) :
    aE k = (aE (cI k))⁻¹ * (qG (cJ k))⁻¹ * aE (cI k) * qG (cJ k) := by
  rw [aE, if_neg (by omega), dif_pos ⟨h1, h2⟩]

theorem cover8 {P : ℕ → Prop} (h0 : ∀ x, 0 ≤ x → x < 0 + 4096 → P x)
    (h1 : ∀ x, 4096 ≤ x → x < 4096 + 4096 → P x) (h2 : ∀ x, 8192 ≤ x → x < 8192 + 4096 → P x)
    (h3 : ∀ x, 12288 ≤ x → x < 12288 + 4096 → P x)
    (h4 : ∀ x, 16384 ≤ x → x < 16384 + 4096 → P x)
    (h5 : ∀ x, 20480 ≤ x → x < 20480 + 4096 → P x)
    (h6 : ∀ x, 24576 ≤ x → x < 24576 + 4096 → P x)
    (h7 : ∀ x, 28672 ≤ x → x < 28672 + 2999 → P x) : ∀ x < 31671, P x := by
  intro x hx
  by_cases a1 : x < 4096
  · exact h0 x (by omega) (by omega)
  by_cases a2 : x < 8192
  · exact h1 x (by omega) (by omega)
  by_cases a3 : x < 12288
  · exact h2 x (by omega) (by omega)
  by_cases a4 : x < 16384
  · exact h3 x (by omega) (by omega)
  by_cases a5 : x < 20480
  · exact h4 x (by omega) (by omega)
  by_cases a6 : x < 24576
  · exact h5 x (by omega) (by omega)
  by_cases a7 : x < 28672
  · exact h6 x (by omega) (by omega)
  exact h7 x (by omega) (by omega)

theorem cover4 {P : ℕ → Prop} (h0 : ∀ x, 0 ≤ x → x < 0 + 8192 → P x)
    (h1 : ∀ x, 8192 ≤ x → x < 8192 + 8192 → P x) (h2 : ∀ x, 16384 ≤ x → x < 16384 + 8192 → P x)
    (h3 : ∀ x, 24576 ≤ x → x < 24576 + 7095 → P x) : ∀ x < 31671, P x := by
  intro x hx
  by_cases a1 : x < 8192
  · exact h0 x (by omega) (by omega)
  by_cases a2 : x < 16384
  · exact h1 x (by omega) (by omega)
  by_cases a3 : x < 24576
  · exact h2 x (by omega) (by omega)
  exact h3 x (by omega) (by omega)

theorem g_tab {j : ℕ} (hj : j < 3) :
    ∀ x < 31671, tb H j x = wv G ((qWords[j]!).map (Nat.add 52)) x := by
  obtain ⟨e0, e1, e2⟩ := qR_eq
  interval_cases j
  · rw [← e0]
    exact cover8 (gTab_spec gReg0_0) (gTab_spec gReg0_1) (gTab_spec gReg0_2)
      (gTab_spec gReg0_3) (gTab_spec gReg0_4) (gTab_spec gReg0_5) (gTab_spec gReg0_6)
      (gTab_spec gReg0_7)
  · rw [← e1]
    exact cover8 (gTab_spec gReg1_0) (gTab_spec gReg1_1) (gTab_spec gReg1_2)
      (gTab_spec gReg1_3) (gTab_spec gReg1_4) (gTab_spec gReg1_5) (gTab_spec gReg1_6)
      (gTab_spec gReg1_7)
  · rw [← e2]
    exact cover8 (gTab_spec gReg2_0) (gTab_spec gReg2_1) (gTab_spec gReg2_2)
      (gTab_spec gReg2_3) (gTab_spec gReg2_4) (gTab_spec gReg2_5) (gTab_spec gReg2_6)
      (gTab_spec gReg2_7)

@[expose] def CF (k x : ℕ) : Prop :=
  tb H k x < 31671 ∧ tb H (cJ k) (tb H (cI k) (tb H k x)) = tb H (cI k) (tb H (cJ k) x)

theorem cReg_spec {k lo c : ℕ} (h : cReg k lo c = true) : ∀ x, lo ≤ x → x < lo + c → CF k x := by
  unfold cReg at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  exact cTab_spec h

theorem c_tab {k : ℕ} (h1 : 3 ≤ k) (h2 : k < 13) : ∀ x < 31671, CF k x := by
  interval_cases k
  · exact cover4 (cReg_spec cReg3_0) (cReg_spec cReg3_1) (cReg_spec cReg3_2) (cReg_spec cReg3_3)
  · exact cover4 (cReg_spec cReg4_0) (cReg_spec cReg4_1) (cReg_spec cReg4_2) (cReg_spec cReg4_3)
  · exact cover4 (cReg_spec cReg5_0) (cReg_spec cReg5_1) (cReg_spec cReg5_2) (cReg_spec cReg5_3)
  · exact cover4 (cReg_spec cReg6_0) (cReg_spec cReg6_1) (cReg_spec cReg6_2) (cReg_spec cReg6_3)
  · exact cover4 (cReg_spec cReg7_0) (cReg_spec cReg7_1) (cReg_spec cReg7_2) (cReg_spec cReg7_3)
  · exact cover4 (cReg_spec cReg8_0) (cReg_spec cReg8_1) (cReg_spec cReg8_2) (cReg_spec cReg8_3)
  · exact cover4 (cReg_spec cReg9_0) (cReg_spec cReg9_1) (cReg_spec cReg9_2) (cReg_spec cReg9_3)
  · exact cover4 (cReg_spec cReg10_0) (cReg_spec cReg10_1) (cReg_spec cReg10_2)
      (cReg_spec cReg10_3)
  · exact cover4 (cReg_spec cReg11_0) (cReg_spec cReg11_1) (cReg_spec cReg11_2)
      (cReg_spec cReg11_3)
  · exact cover4 (cReg_spec cReg12_0) (cReg_spec cReg12_1) (cReg_spec cReg12_2)
      (cReg_spec cReg12_3)

theorem qG_acts
    {j : ℕ} (hj : j < 3) :
    ∀ x < 31671, tb H j x = idx 31671 (qG j) x := by
  intro x hx
  rw [g_tab hj x hx, wvG_eq _ (chain_ok (qWords_lt j hj)) x hx, chain_prod]
  rfl

theorem aE_acts :
    ∀ k < 13, ∀ x < 31671, tb H k x = idx 31671 (aE k) x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    by_cases h3 : k < 3
    · rw [aE_lt3 h3]
      exact qG_acts h3 x hx
    have hk3 : 3 ≤ k := by omega
    have hi := cI_lt hk3
    have hj := cJ_lt k
    obtain ⟨hy, e⟩ := c_tab hk3 hk x hx
    have ai : ∀ z < 31671, tb H (cI k) z = idx 31671 (aE (cI k)) z := ih (cI k) hi (by omega)
    have gj : ∀ z < 31671, tb H (cJ k) z = idx 31671 (qG (cJ k)) z := qG_acts hj
    rw [ai _ hy, gj _ (idx_lt _ hy), gj x hx, ai _ (idx_lt _ hx), ← idx_mul, ← idx_mul] at e
    have eg : (qG (cJ k) * aE (cI k))⁻¹ * (aE (cI k) * qG (cJ k)) = aE k := by
      rw [aE_comm hk3 hk]
      group
    rw [← eg, idx_mul, ← e, idx_inv_idx]

theorem cr_conj_aE :
    ∀ q < 198, ∃ c : Fin 4, IsConj (((nwR 13 (f32 CR q)).map aE).prod) (t3 c) :=
  cr_conj aE aE_acts

theorem conj_t3_aE
    {q : ℕ} (hq : q < 198) {x w : CFSG.Sporadic.Fi23.J}
    (h : x * w = w * ((nwR 13 (f32 CR q)).map aE).prod) : ∃ c : Fin 4, IsConj x (t3 c) :=
  conj_t3_of aE aE_acts hq h

end CertificateChecks.KernelFi23Q

end
