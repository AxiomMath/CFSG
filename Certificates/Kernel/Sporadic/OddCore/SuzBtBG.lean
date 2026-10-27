
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtVG
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtBG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG
  CertificateChecks.KernelSpor.SuzBtVG

@[expose] noncomputable def apL (i j p : Nat) : Nat :=
  nIf(Nat.beq (Nat.land (Nat.shiftRight i j) 1) 1, pg 11 (mask 11) (SuzBtL1.G j) p, p)

@[expose] noncomputable def l1E (i p : Nat) : Nat := apL i 0 (apL i 1 (apL i 2 (apL i 3 p)))

@[expose] noncomputable def TB (j : Nat) : Nat :=
  nIf(Nat.beq j 0, 17274361803683611920, 9929781798390354960)

@[expose] noncomputable def f6bK (T N : Nat) : Bool :=
  allN 16 (fun i => allN 3 (fun t => Nat.beq (pg 11 (mask 11) N (l1E i (pg 11 (mask 11) SuzBtL1.B t)))
    (l1E (pg 4 15 T i) (pg 11 (mask 11) N (pg 11 (mask 11) SuzBtL1.B t)))))

theorem kF6b : allN 2 (fun j => f6bK (TB j) (decK (ntl1Decs.getD j ([], 0)))) = true := by
  quickRfl

theorem bit_eq : ∀ i < 16, ∀ j < 4, Nat.beq (Nat.land (Nat.shiftRight i j) 1) 1 = Nat.testBit i j := by
  decide

theorem TB_eq : ∀ j < 2, ∀ i < 16, pg 4 15 (TB j) i = (tbarTabs[j]!)[i]! := by
  decide +kernel

theorem lb_eq {j : Nat} (hj : j < 4) : l1BasisPerm j = lgp j := by
  interval_cases j <;> rfl

noncomputable def fac (i : Fin 16) (j : Nat) : Equiv.Perm (Fin 1782) :=
  if i.val.testBit j then lgp j else 1

theorem l1Elt_eq (i : Fin 16) : l1Elt i = fac i 0 * (fac i 1 * (fac i 2 * fac i 3)) := by
  simp only [l1Elt, fac, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [lb_eq (by norm_num : 0 < 4), lb_eq (by norm_num : 1 < 4), lb_eq (by norm_num : 2 < 4),
    lb_eq (by norm_num : 3 < 4)]

theorem fac_mem (i : Fin 16) {j : Nat} (hj : j < 4) : fac i j ∈ genSub 1782 4 lgp := by
  unfold fac
  split
  · exact gp_mem hj
  · exact Subgroup.one_mem _

theorem l1Elt_mem (i : Fin 16) : l1Elt i ∈ invE 1 := by
  rw [l1Elt_eq]
  refine l1_le (Subgroup.mul_mem _ (fac_mem i (by norm_num)) (Subgroup.mul_mem _
    (fac_mem i (by norm_num)) (Subgroup.mul_mem _ (fac_mem i (by norm_num))
      (fac_mem i (by norm_num)))))

theorem apL_eq (i : Fin 16) {j : Nat} (hj : j < 4) (p : Fin 1782) :
    apL i j p = (fac i j p : Nat) := by
  unfold apL fac
  rw [bit_eq i i.isLt j hj]
  rcases Bool.eq_false_or_eq_true (i.val.testBit j) with h | h
  · rw [h, if_pos rfl]
    exact hgL j hj p
  · rw [h, if_neg (by simp)]
    rfl

theorem l1E_eq (i : Fin 16) (p : Fin 1782) : l1E i p = (l1Elt i p : Nat) := by
  unfold l1E
  rw [apL_eq i (by norm_num) p, apL_eq i (by norm_num), apL_eq i (by norm_num),
    apL_eq i (by norm_num), l1Elt_eq]
  simp only [Equiv.Perm.mul_apply]

theorem ntl1Decs_ok' {j : Nat} (hj : j < 2) : (∀ k ∈ (ntl1Decs.getD j ([], 0)).1, k < 10) ∧
    (ntl1Decs.getD j ([], 0)).2 < 128 :=
  ntl1Decs_ok (by omega)

theorem conj_l1Elt {j : Nat} (hj : j < 2) (i : Fin 16) :
    decPerm (ntl1Decs.getD j ([], 0)) * l1Elt i * (decPerm (ntl1Decs.getD j ([], 0)))⁻¹ =
      l1Elt (tabPerm16 tbarTabs[j]! i) := by
  set ν := decPerm (ntl1Decs.getD j ([], 0))
  have hν : ∀ x : Fin 1782, pg 11 (mask 11) (decK (ntl1Decs.getD j ([], 0))) x = ν x :=
    pg_decK (ntl1Decs_ok' hj).1 (ntl1Decs_ok' hj).2
  have hνm : ν ∈ invE 1 := decPerm_mem (ntl1Decs_ok' hj).1
  have hb : (tbarTabs[j]!)[i.val]! < 16 := by
    rw [(f9_tabRep_tbar j hj).2 i]
    exact (tabPerm16 tbarTabs[j]! i).isLt
  have hti : tabPerm16 tbarTabs[j]! i = ⟨(tbarTabs[j]!)[i.val]!, hb⟩ :=
    Fin.ext ((f9_tabRep_tbar j hj).2 i).symm
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kF6b j hj
  rw [mul_inv_eq_iff_eq_mul]
  refine invE1_ext (Subgroup.mul_mem _ hνm (l1Elt_mem i))
    (Subgroup.mul_mem _ (l1Elt_mem _) hνm) fun t => Fin.ext ?_
  have e := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h i i.isLt) t t.2)
  rw [hbL t, l1E_eq i, hν, hν, TB_eq j hj i i.isLt] at e
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hti]
  rw [← l1E_eq ⟨(tbarTabs[j]!)[i.val]!, hb⟩]
  exact e

theorem f6bProp : F6bProp := by
  unfold F6bProp
  intro j hj
  refine ⟨decPerm (ntl1Decs.getD j ([], 0)), ?_, conj_l1Elt hj⟩
  rw [tabSubgroup_v0Tabs]
  exact (nt_facts (by omega)).1

end CertificateChecks.KernelSpor.SuzBtBG

end
