module

public import Certificates.Kernel.Fi23Y322.ChkDefs
public import Certificates.Kernel.Fi23Cls.Glue
public import CFSG.Certificates.Kernel.Fi23Y322.Sound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
public import Certificates.Data.TabFi23Y
public meta import Certificates.Data.TabFi23Y
import Certificates.Kernel.Fi23Y322.Chk
import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Y322

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native
  CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.KC.Fi23Five CFSG.KC.Fi23Y322 CFSG.KD.Fi23Y322
  CertificateChecks.KernelFi23Q CertificateChecks.KernelFi23Cls
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Dickson.I271.TabFi23Y
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem tW_eq : ∀ u : List ℕ, (∀ k ∈ u, k < 31671) →
    ∀ x < 31671, tW G u x = idx 31671 (u.map conjPt).prod x
  | [], _, x, _ => by
    rw [tW_nil, List.map_nil, List.prod_nil, idx_one]
  | k :: u, hu, x, hx => by
    have hk : k < 31671 := hu k List.mem_cons_self
    rw [tW_cons, tW_eq u (fun j hj => hu j (List.mem_cons_of_mem k hj)) x hx,
      ← conjPt_acts hk _ (idx_lt _ hx), List.map_cons, List.prod_cons, idx_mul]

theorem prod_eq_one {u : List ℕ} (hu : ∀ k ∈ u, k < 31671) (h : ∀ t < 6, tW G u t = t) :
    (u.map conjPt).prod = 1 :=
  eq_of_base fun t ht => by
    rw [idx_one, ← tW_eq u hu t (by omega)]
    exact h t ht

theorem relW_eq : yRelsD.map (fun w => w.map fun c => y322Ks[c]!) = yWords := by decide

theorem yWords_lt : ∀ u ∈ yWords, ∀ k ∈ u, k < 31671 := by decide

theorem ks_eq : y322Ks = ks := rfl

theorem w0_eq' : CFSG.KD.Fi23Q.t3R 0 = CFSG.KD.Fi23Y322.w0 := by decide

theorem yCheck_ok :
    yCheck orb (dTable orb) (genTables orb (-2)) (t3Tabs orb letters)[0]! y322Ks = true := by
  have hk : yK G CFSG.KD.Fi23Y322.w0 ks yWords 31036 4160 = true := ch17339y_ok
  obtain ⟨hfix, hwords, hnc⟩ := yK_spec hk
  have hT : Rep 31671 (t3Tabs orb letters)[0]! (t3 0) := rep_t3Tabs 0
  have hact := act_t3 (c := 0) (by norm_num) w0_eq'
  unfold yCheck
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by decide, by decide⟩, ?_⟩, by decide⟩, ?_⟩, ?_⟩
  · intro k hk
    rw [ks_eq] at hk
    obtain ⟨hk1, hk2⟩ := hfix k hk
    rw [hT k hk1]
    have h1 := hact k hk1
    rw [hk2] at h1
    exact h1.symm
  · intro w hw
    have hmem : w.map (fun c => y322Ks[c]!) ∈ yWords := by
      rw [← relW_eq]
      exact List.mem_map_of_mem hw
    have h1 := prod_eq_one (yWords_lt _ hmem) (hwords _ hmem)
    have h2 := rep_starWordTab_dTable (w.map fun c => y322Ks[c]!)
    rw [h1] at h2
    exact eqTab_of_rep_eq h2 (Rep.idT (by norm_num))
  · cases e : eqTab (starWordTab orb (dTable orb) (genTables orb (-2)) [y322Ks[0]!, y322Ks[1]!])
        (starWordTab orb (dTable orb) (genTables orb (-2)) [y322Ks[1]!, y322Ks[0]!])
    · rfl
    · exfalso
      have h1 := eq_of_eqTab (rep_starWordTab_dTable _) (rep_starWordTab_dTable _) e
      have e0 : y322Ks[0]! = 31036 := rfl
      have e1 : y322Ks[1]! = 4160 := rfl
      simp only [e0, e1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one] at h1
      rw [(cmK_iff (by norm_num) (by norm_num)).2 h1.symm] at hnc
      cases hnc

end CertificateChecks.KernelFi23Y322

end
