
module

public import Certificates.Kernel.Ly3085.Facts3085Base

public import Certificates.Kernel.Ly3085.FixCount
public import CFSG.RankThree.PartOne.KS.LyFiveGeneric

public section

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega
open MulAction

section

variable [LySeed]

theorem stabilizer_omE : stabilizer J omE = lyH := by
  rw [← F1.1]
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  exact Subtype.ext_iff

theorem exists_subO (y : orbit J opE) : ∃ i, y.1 ∈ subO i := by
  classical
  have h := F1_all.2.1
  have hy : y.1 ∈ ((Finset.univ.biUnion subO : Finset LyOperator) : Set LyOperator) := by
    rw [h]; exact y.2
  simpa using hy

@[expose] def lab (y : orbit J opE) : Fin 5 := Classical.choose (exists_subO y)

theorem subO_unique {y : LyOperator} {i j : Fin 5} (hi : y ∈ subO i) (hj : y ∈ subO j) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.1 (F1_all.2.2.1 hij) hi hj

theorem lab_spec (y : orbit J opE) : y.1 ∈ subO (lab y) := Classical.choose_spec (exists_subO y)

theorem lab_eq_iff (y : orbit J opE) (i : Fin 5) : lab y = i ↔ y.1 ∈ subO i :=
  ⟨fun h => h ▸ lab_spec y, fun h => subO_unique (lab_spec y) h⟩

theorem lab_omE : lab omE = 0 := by
  rw [lab_eq_iff, mem_subO_iff, Fin.val_zero, repOp_zero]
  exact mem_orbit_self opE

theorem card_lab (i : Fin 5) [Fintype (orbit J opE)] :
    (Finset.univ.filter (fun p : orbit J opE => lab p = i)).card = subSizes i := by
  classical
  have hsub : ∀ y ∈ subO i, y ∈ orbit J opE := by
    intro y hy
    have h := F1_all.2.1
    have : y ∈ ((Finset.univ.biUnion subO : Finset LyOperator) : Set LyOperator) := by
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Set.mem_iUnion, Finset.mem_coe]
      exact ⟨i, hy⟩
    rw [h] at this
    exact this
  have e : (Finset.univ.filter (fun p : orbit J opE => lab p = i)).card = (subO i).card := by
    refine Finset.card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p _ q _ e => Subtype.ext e)
      (fun y hy => ⟨⟨y, hsub y hy⟩, ?_, rfl⟩)
    · exact (lab_eq_iff p i).1 (Finset.mem_filter.1 hp).2
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (lab_eq_iff _ i).2 hy⟩
  rw [e, card_subO]
  obtain ⟨-, -, -, h0, h1, h2, h3, h4⟩ := F1_all
  fin_cases i
  · change Nat.card (orbit lyH (repOp 0)) = 1
    rw [repOp_zero]; exact h0
  · change Nat.card (orbit lyH (repOp 1)) = 19530
    rw [repOp_pos (by decide)]; exact h1
  · change Nat.card (orbit lyH (repOp 2)) = 968750
    rw [repOp_pos (by decide)]; exact h2
  · change Nat.card (orbit lyH (repOp 3)) = 2034375
    rw [repOp_pos (by decide)]; exact h3
  · change Nat.card (orbit lyH (repOp 4)) = 5812500
    rw [repOp_pos (by decide)]; exact h4

theorem isPreprimitive_omega : IsPreprimitive J (orbit J opE) := by
  classical
  have hfin : Finite (orbit J opE) :=
    Nat.finite_of_card_ne_zero (by rw [F1.2.2]; norm_num)
  let _ : Fintype (orbit J opE) := Fintype.ofFinite _
  refine CFSG.Sporadic.Th.isPreprimitive_of_suborbit_labels omE lyH (fun h hh => ?_) lab
    (fun h hh p => ?_) (fun p q hpq => ?_) (fun S hS hdvd => ?_)
  · rw [← stabilizer_omE] at hh
    exact hh
  · rw [lab_eq_iff]
    exact smul_mem_subO hh (lab_spec p)
  · have hp := (mem_subO_iff _ _).1 (lab_spec p)
    have hq := (mem_subO_iff _ _).1 (hpq ▸ lab_spec q)
    obtain ⟨⟨u, hu⟩, hup⟩ := hp
    obtain ⟨⟨v, hv⟩, hvq⟩ := hq
    refine ⟨v * u⁻¹, lyH.mul_mem hv (lyH.inv_mem hu), Subtype.ext ?_⟩
    change (v * u⁻¹) • p.1 = q.1
    rw [← hup, ← hvq]
    change (v * u⁻¹) • (u • repOp (lab p).val) = v • repOp (lab p).val
    rw [← mul_smul, inv_mul_cancel_right]
  · rw [lab_omE] at hS ⊢
    have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : orbit J opE => lab p = i)).card) =
        ∑ i ∈ S, subSizes i := Finset.sum_congr rfl fun i _ => card_lab i
    have hcard : Fintype.card (orbit J opE) = 8835156 := by
      rw [Fintype.card_eq_nat_card, F1.2.2]
    rw [hsum, hcard] at hdvd
    exact subSizes_blocks S hS hdvd

theorem orderOf_lyYB : orderOf lyYB = 3 := by
  obtain ⟨-, k1, -, -⟩ := class_facts
  have k : restr7 lyYB ^ 3 = 1 ∧ restr7 lyYB ≠ 1 := by
    unfold cls at k1
    simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] at k1
    exact ⟨k1.1, k1.2.1⟩
  have hY : lyYB ∈ lyH := wordJ_mem _
  have hS := lyH_le_stabU hY
  have e3 : restr7 (lyYB * lyYB * lyYB) = restr7 1 := by
    rw [restr7_mul (stabU.mul_mem hS hS) hS, restr7_mul hS hS, restr7_one, ← k.1]
    rw [pow_succ, pow_two]
  have hpow : lyYB ^ 3 = 1 := by
    rw [pow_succ, pow_two]
    exact restr7_inj F1.2.1.le (lyH.mul_mem (lyH.mul_mem hY hY) hY) lyH.one_mem e3
  have hne : lyYB ≠ 1 := fun e => k.2 (by rw [e, restr7_one])
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime hpow hne

theorem lyFacts : LyFacts := by
  refine ⟨card_J_S, isSimpleGroup_J_S, F1.1, F1.2.1, F1.2.2, isPreprimitive_omega, lyt_fix,
    fix_counts.1, fix_counts.2.1, fix_counts.2.2.1, fix_counts.2.2.2, orderOf_lyYB, ?_⟩
  have hY : lyYB ∈ lyH := wordJ_mem _
  rw [CFSG.RankThree.PartOne.card_centralizer_inf_eq lyH lyYB hY]
  exact card_centralizer_yB

end

end CertificateChecks.KernelLy.Omega

end
