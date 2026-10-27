
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtZG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtNF
public import Certificates.Kernel.Sporadic.OddCore.SuzBtNC
public import CFSG.Certificates.Kernel.Spor.BTupNSound
public import CFSG.Sporadic.SuzRecog.SuzL34Cert.SoundCommon
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtNG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG

theorem kBC : allN 4 (fun j => Nat.beq (SuzBtCL1.G j) (decK (cl1Decs.getD j ([], 0)))) = true := by
  quickRfl

theorem kN : allN 2 (fun j => strictB (decK (nl1Decs.getD j ([], 0))) (fun N =>
    allN 4 (fun i => btNrK 11 (mask 11) 3 4 SuzBtL1.G SuzBtL1.B N (SuzBtL1.G i)))) = true := by
  quickRfl

@[expose] noncomputable def cgp (j : Nat) : Equiv.Perm (Fin 1782) :=
  decPerm (cl1Decs.getD j ([], 0))

@[expose] noncomputable def ngp (j : Nat) : Equiv.Perm (Fin 1782) :=
  decPerm (nl1Decs.getD j ([], 0))

theorem cl1Decs_ok {i : Nat} (hi : i < 4) : (∀ k ∈ (cl1Decs.getD i ([], 0)).1, k < 10) ∧
    (cl1Decs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem nl1Decs_ok {i : Nat} (hi : i < 2) : (∀ k ∈ (nl1Decs.getD i ([], 0)).1, k < 10) ∧
    (nl1Decs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem hgC : ∀ j < 4, ∀ x : Fin 1782, pg 11 (mask 11) (SuzBtCL1.G j) x = cgp j x :=
  fun j hj x => by
    rw [Nat.eq_of_beq_eq_true (allN_spec kBC j hj)]
    exact pg_decK (cl1Decs_ok hj).1 (cl1Decs_ok hj).2 x

theorem hbC : ∀ t : Fin 3, pg 11 (mask 11) SuzBtCL1.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem hpC : ∀ i < SuzBtCL1.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtCL1.cnt
    SuzBtCL1.B SuzBtCL1.G SuzBtCL1.K SuzBtCL1.R SuzBtCL1.POS i = true := by
  intro i hi
  have hi' := hi
  rw [SuzBtNF.kCnt] at hi'
  rcases Nat.lt_or_ge i 1024 with h1 | h1
  · exact btSl_spec SuzBtNF.kSl0 (by omega) (by omega) hi
  · rcases Nat.lt_or_ge i 2048 with h2 | h2
    · exact btSl_spec SuzBtNF.kSl1 (by omega) (by omega) hi
    · exact btSl_spec SuzBtNF.kSl2 (by omega) (by omega) hi

theorem cl1_eq : genSub 1782 4 cgp = decSubgroup cl1Decs := genSub_dec cl1Decs

theorem nl1_eq : genSub 1782 2 ngp = decSubgroup nl1Decs := genSub_dec nl1Decs

theorem cl1_le : genSub 1782 4 cgp ≤ invE 1 := by
  rw [cl1_eq]
  exact decSubgroup_le_invE (by decide)

theorem nl1_le : genSub 1782 2 ngp ≤ invE 1 := by
  rw [nl1_eq]
  exact decSubgroup_le_invE (by decide)

theorem card_CL1 : Nat.card (decSubgroup cl1Decs) = 3072 := by
  rw [← cl1_eq, ← SuzBtNF.kCnt]
  exact card_genSub_of_btK (w := 11) (kw := 33) (km := mask 33) (K := SuzBtCL1.K)
    (R := SuzBtCL1.R) (POS := SuzBtCL1.POS) (by norm_num) cl1_le hgC hbC SuzBtNF.kHd hpC

theorem gen_comm {j l : Nat} (hj : j < 4) (hl : l < 4) : cgp j * lgp l = lgp l * cgp j := by
  refine invE1_ext (Subgroup.mul_mem _ (cl1_le (gp_mem hj)) (l1_le (gp_mem hl)))
    (Subgroup.mul_mem _ (l1_le (gp_mem hl)) (cl1_le (gp_mem hj))) fun t => Fin.ext ?_
  have h := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1
    (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtNF.kC j hj) l hl) t t.2)
  rw [hbC t, hgL l hl, hgC j hj, hgC j hj, hgL l hl] at h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact h

theorem cl1_le_cent : decSubgroup cl1Decs ≤
    Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) := by
  rw [← cl1_eq, ← l1_eq]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  have hle : genSub 1782 4 lgp ≤ Subgroup.centralizer {cgp j} := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact gen_comm hj hl
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.1 (hle hy)) _ rfl).symm

theorem cl1_le_inf : decSubgroup cl1Decs ≤
    Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) ⊓ invE 1 :=
  le_inf cl1_le_cent (cl1_eq ▸ cl1_le)

theorem hgN {j : Nat} (hj : j < 2) : ∀ x : Fin 1782,
    pg 11 (mask 11) (decK (nl1Decs.getD j ([], 0))) x = ngp j x :=
  pg_decK (nl1Decs_ok hj).1 (nl1Decs_ok hj).2

theorem conj_gen_mem {j i : Nat} (hj : j < 2) (hi : i < 4) :
    ngp j * lgp i * (ngp j)⁻¹ ∈ genSub 1782 4 lgp := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kN j hj
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  obtain ⟨l, hl, he⟩ := btNr_spec hgL (hgN hj) (hgL i hi) hbL (CFSG.KS.Raw.Orb.allN_iff.1 h i hi)
  have hn := nl1_le (gp_mem hj)
  have e : ngp j * lgp i = l * ngp j :=
    invE1_ext (Subgroup.mul_mem _ hn (l1_le (gp_mem hi))) (Subgroup.mul_mem _ (l1_le hl) hn)
      fun t => he t
  rw [e, mul_inv_cancel_right]
  exact hl

theorem nl1_le_norm : decSubgroup nl1Decs ≤
    Subgroup.normalizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) := by
  rw [← nl1_eq, ← l1_eq]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  refine mem_set_normalizer_of_finite (Set.toFinite _) fun x hx => ?_
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    exact conj_gen_mem hj hi
  | one => simpa using Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    have e : ngp j * (a * b) * (ngp j)⁻¹ =
        (ngp j * a * (ngp j)⁻¹) * (ngp j * b * (ngp j)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : ngp j * a⁻¹ * (ngp j)⁻¹ = (ngp j * a * (ngp j)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem conj_m1_gen {j l : Nat} (hj : j < 4) (hl : l < 8) :
    (cgp j)⁻¹ * mgp l * cgp j ∈ genSub 1782 8 mgp := by
  obtain ⟨x, hx, he⟩ := btCj_spec hgM hbM hpM (hgC j hj) (hgM l hl) hbM
    (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtNC.kCj j hj) l hl)
  have hc := cl1_le (gp_mem hj)
  have e : cgp j * x = mgp l * cgp j :=
    invE1_ext (Subgroup.mul_mem _ hc (m1_le hx)) (Subgroup.mul_mem _ (m1_le (gp_mem hl)) hc)
      fun t => he t
  rw [mul_assoc, ← e, inv_mul_cancel_left]
  exact hx

theorem cl1_le_norm_m1 : decSubgroup cl1Decs ≤
    Subgroup.normalizer (decSubgroup m1Decs : Set (Equiv.Perm (Fin 1782))) := by
  rw [← cl1_eq, ← (show genSub 1782 8 mgp = decSubgroup m1Decs from genSub_dec m1Decs)]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  refine (Subgroup.inv_mem_iff _).1 (mem_set_normalizer_of_finite (Set.toFinite _) fun x hx => ?_)
  rw [SetLike.mem_coe] at hx ⊢
  rw [inv_inv]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact conj_m1_gen hj hl
  | one => simpa using Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    have e : (cgp j)⁻¹ * (a * b) * cgp j =
        ((cgp j)⁻¹ * a * cgp j) * ((cgp j)⁻¹ * b * cgp j) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : (cgp j)⁻¹ * a⁻¹ * cgp j = ((cgp j)⁻¹ * a * cgp j)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem m1_normal : ((decSubgroup m1Decs).subgroupOf (decSubgroup cl1Decs)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hcoe : ((g * n * g⁻¹ : ↥(decSubgroup cl1Decs)) : Equiv.Perm (Fin 1782)) =
      (g : Equiv.Perm (Fin 1782)) * (n : Equiv.Perm (Fin 1782)) *
        (g : Equiv.Perm (Fin 1782))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]
  exact (Subgroup.le_normalizer_iff.mp cl1_le_norm_m1) g g.2 n hn

end CertificateChecks.KernelSpor.SuzBtNG

end
