module

public import Certificates.Kernel.J4ZC9686.Checks
public import Certificates.Kernel.J4R0.Facts
public import CFSG.Certificates.Kernel.J4ZC9686Sound
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gen

public section

set_option maxRecDepth 4000

namespace CertificateChecks.KernelJ4ZC9686

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.ZCent CFSG.Quasithin.J4ZCent
open CFSG.Quasithin.J4M2 (gE cE Kgrp Qgrp)
open CFSG.KC.J4Q (mulJ getN wordJ letJ)
open CFSG.KC.J4ZC9686 CFSG.KD.J4Q CertificateChecks.KernelJ4R0
open CertificateChecks.KernelJ4Count.FixCE (PR PR_one PR_mul PR_eq PR_gE_q PR_cE)
open CFSG.KC.PcChain (wfrom)

theorem b0El_mem' {i : ℕ} (hi : i < 16) : b0El i ∈ B0 :=
  Subgroup.subset_closure (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

theorem tW_ok' : ∀ i < 60, WordOK 16 (tW.getD i []) := by
  unfold WordOK
  decide

theorem rW_ok' : ∀ j < 15, WordOK 16 (rW.getD j []) := by
  unfold WordOK
  decide

theorem tEl_mem' {i : ℕ} (hi : i < 60) : tEl i ∈ B0 :=
  mem_of_evalW b0El (fun _ hn => b0El_mem' hn) (tW_ok' i hi)

theorem R0_le_B0' : R0 ≤ B0 := by
  rw [R0, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  exact mem_of_evalW b0El (fun _ hn => b0El_mem' hn) (rW_ok' j (List.mem_range.1 hj))

theorem b_inv {n : ℕ} (hn : n < 16) (h3 : n ≠ 3) (h4 : n ≠ 4) : (b0El n)⁻¹ = b0El n := by
  have hb := PR_b0El hn
  have hc : PR (b0El n * b0El n) one := by
    rw [← invOK_spec ch9686inv n hn h3 h4]
    exact PR_mul hb hb
  exact inv_eq_of_mul_eq_one_right (PR_eq hc PR_one)

theorem PR_BI {n : ℕ} (hn : n < 16) : PR (b0El n)⁻¹ (getN one BI n) := by
  by_cases h3 : n = 3
  · subst h3
    exact PR_b3i
  by_cases h4 : n = 4
  · subst h4
    exact PR_b4i
  rw [b_inv hn h3 h4]
  have e : getN one BI n = getN one BS n := by
    interval_cases n <;> first | rfl | omega
  rw [e]
  exact PR_b0El hn

theorem perf_letters : ∀ i < 16, ∀ l ∈ perfWord (perfW.getD i []),
    (∃ n < 16, l = Int.ofNat (n + 1)) ∨ ∃ n < 16, l = Int.negSucc n := by
  decide

theorem perfW_ok' : ∀ i < 16, ∀ p ∈ perfW.getD i [], WordOK 16 p.1 ∧ WordOK 16 p.2 := by
  unfold WordOK
  decide

theorem perf_eq {i : ℕ} (hi : i < 16) : b0El i = evalW b0El (perfWord (perfW.getD i [])) := by
  refine PR_eq' (PR_b0El hi) (PR_wordJ (mats := BS) (invs := BI) fun l hl => ?_)
    (perfOK_spec ch9686perf i hi).symm
  rcases perf_letters i hi l hl with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · rw [KernelJ4R0.letterOf_pos]
    change PR (b0El n) (getN one BS n)
    exact PR_b0El hn
  · rw [KernelJ4R0.letterOf_neg]
    change PR (b0El n)⁻¹ (getN one BI n)
    exact PR_BI hn

theorem B0_perfect : ⁅B0, B0⁆ = B0 := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb)
  · rw [B0, Subgroup.closure_le]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi' := List.mem_range.1 hi
    rw [SetLike.mem_coe, perf_eq hi']
    exact evalW_perfWord_mem b0El (fun _ hn => b0El_mem' hn) _ (perfW_ok' i hi')

theorem conj_mem_of_gens {g : J} (h : ∀ i < 16, g * b0El i * g⁻¹ ∈ B0) {x : J} (hx : x ∈ B0) :
    g * x * g⁻¹ ∈ B0 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    exact h i (List.mem_range.1 hi)
  | one => simp
  | mul x y _ _ ihx ihy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ih

theorem conj_gens {q : J} {Q : ℕ} (hq : PR q Q) {W : List (ℕ × ℕ)}
    (h : knOK c rm one XS BS TS Q W = true) : ∀ j < 16, q * b0El j * q⁻¹ ∈ B0 := by
  intro j hj
  obtain ⟨hlt, he⟩ := knOK_spec h j hj
  have e := PR_eq' (PR_mul hq (PR_b0El hj))
    (PR_mul (PR_mul (PR_tEl hlt) (PR_wfrom 15 0 (W.getD j (0, 0)).2 (by norm_num))) hq) he
  have e2 : q * b0El j * q⁻¹ = tEl (W.getD j (0, 0)).1 * wfrom xE (W.getD j (0, 0)).2 0 15 := by
    rw [e]
    group
  rw [e2]
  exact Subgroup.mul_mem _ (tEl_mem' hlt) (R0_le_B0' (wfrom_mem_R0 _))

theorem kn_all : ∀ k < 13, ch9686kn k = true := by
  intro k hk
  interval_cases k
  exacts [ch9686kn0, ch9686kn1, ch9686kn2, ch9686kn3, ch9686kn4, ch9686kn5, ch9686kn6, ch9686kn7,
    ch9686kn8, ch9686kn9, ch9686kn10, ch9686kn11, ch9686kn12]

theorem QL_eq {k : ℕ} (hk : k < 12) :
    getN one QL k = getN one CertificateChecks.KernelJ4Q.QAs k := by
  interval_cases k <;> rfl

theorem conj_gE {k : ℕ} (hk : k < 12) {x : J} (hx : x ∈ B0) : gE k * x * (gE k)⁻¹ ∈ B0 := by
  have hq := PR_gE_q hk
  rw [← QL_eq hk] at hq
  exact conj_mem_of_gens (conj_gens hq (kn_all k (by omega))) hx

theorem conj_cE {x : J} (hx : x ∈ B0) : cE * x * cE⁻¹ ∈ B0 := by
  have hq : PR cE (getN one QL 12) := PR_cE
  exact conj_mem_of_gens (conj_gens hq (kn_all 12 (by norm_num))) hx

theorem Kgrp_le_normalizer : Kgrp ≤ Subgroup.normalizer (B0 : Set J) := by
  have hQ : Qgrp ≤ Subgroup.normalizer (B0 : Set J) := by
    rw [Qgrp, Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.mem_normalizer_fintype fun y hy => conj_gE hn hy
  have hc : Subgroup.zpowers cE ≤ Subgroup.normalizer (B0 : Set J) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_fintype fun y hy => conj_cE hy
  exact sup_le hQ hc

end CertificateChecks.KernelJ4ZC9686
