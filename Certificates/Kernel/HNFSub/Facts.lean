module

public import Certificates.Kernel.HNFFib.Facts
public import Certificates.Kernel.HNFSub.Chk0
public import Certificates.Kernel.HNFSub.Chk1
public import Certificates.Kernel.HNFSub.Chk2
public import Certificates.Kernel.HNFSub.Chk3
public import Certificates.Kernel.HNFSub.Chk4
public import Certificates.Kernel.HNFSub.Chk5
public import Certificates.Kernel.HNFSub.Chk6
public import Certificates.Kernel.HNFSub.Chk7
public import Certificates.Kernel.HNFSub.Chk8
public import Certificates.Kernel.HNFSub.Chk9
public import Certificates.Kernel.HNFSub.Chk10
public import Certificates.Kernel.HNFSub.Chk11
public import Certificates.Kernel.HNFSub.Chk12
public import Certificates.Kernel.HNFSub.Chk13
public import Certificates.Kernel.HNFSub.Chk14
public import Certificates.Kernel.HNFSub.Base
public import Certificates.Kernel.HNFSub.Dist
public import CFSG.Certificates.Kernel.HNFSubSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFOrb
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelHNFSub

open CFSG.EvenSporadicStandard.Solomon78

#kc_forall_tree segsOK (fun i => CFSG.KD.HNFSub.segW hnfW1 hnfW2 i = true) 347 CFSG.KD.HNFSub.c

theorem segs_length : CFSG.KD.HNFSub.S7.segs.length = 347 := by
  have h : Nat.beq CFSG.KD.HNFSub.S7.segs.length 347 = true := by quickRfl
  exact Nat.eq_of_beq_eq_true h

open CFSG.Sporadic.HNSchreier CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib CFSG.KS.HNF26729
  CFSG.KS.HNFFib
open CFSG.KS.HNLocal CFSG.KS.HNFSub CertificateChecks.KernelHNF26720
open CertificateChecks.KernelHNF26729 CertificateChecks.KernelHNFFib

local notation "RA" => CFSG.KD.FamHNSeed.RW 1
local notation "RB" => CFSG.KD.FamHNSeed.RW 2
local notation "BI" => CFSG.KD.HNF26729.Bi
local notation "β7" => hnfRep hnfRepWords[7]!

theorem cBi' : CFSG.KS.Ord.Canon 5 133 13 CFSG.KD.HNF26729.Bi := cBi

theorem comm_gen {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
    (hρ : Function.Injective ρ) (a g1 g2 : G) (h1 : ρ a * ρ g1 = ρ g1 * ρ a)
    (h2 : ρ a * ρ g2 = ρ g2 * ρ a) :
    ∀ c ∈ Subgroup.closure ({a, g1, g2} : Set G), ρ c * ρ a = ρ a * ρ c := by
  have hCa := comm_of_closure a g1 g2
    (hρ (by rw [map_mul ρ g1 a, map_mul ρ a g1]; exact h1.symm))
    (hρ (by rw [map_mul ρ g2 a, map_mul ρ a g2]; exact h2.symm))
  intro c hc
  rw [← map_mul, ← map_mul, hCa c hc]

theorem p_comm : ∀ c ∈ hnfC0, ρJ c * ρJ aJ = ρJ aJ * ρJ c := by
  obtain ⟨hr0, -⟩ := base_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.base
  obtain ⟨hA1, hA2, -⟩ := fibU_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.fib hr0
  have hg1 : ρJ hnfG1 = MW RA RB BI hnfW1 := (mw_eq w1_valid).symm
  have hg2 : ρJ hnfG2 = MW RA RB BI hnfW2 := (mw_eq w2_valid).symm
  exact comm_gen ρJ ρJ_injective aJ hnfG1 hnfG2 (by rw [ρ_aJ, hg1]; exact hA1)
    (by rw [ρ_aJ, hg2]; exact hA2)

theorem p_U : spanR CFSG.KD.HNFSub.S7.r0 = Uof (ρJ aJ) (ρJ β7) := by
  obtain ⟨-, hU⟩ := base_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.base
  rw [hU, ρ_aJ, ρ_rep (i := 7) (by norm_num)]

theorem p_G0 : ∃ c ∈ hnfC0, ρJ c = MW RA RB BI (invW hnfW1) := by
  refine ⟨wordProd hnfGen [-2], mem_C0 (by decide), ?_⟩
  rw [ρ_stab [-2] (by decide), MS, List.map_singleton, List.prod_singleton, ltr3_neg_two]

theorem p_G1 : ∃ c ∈ hnfC0, ρJ c = MW RA RB BI (invW hnfW2) := by
  refine ⟨wordProd hnfGen [-3], mem_C0 (by decide), ?_⟩
  rw [ρ_stab [-3] (by decide), MS, List.map_singleton, List.prod_singleton, ltr3_neg_three]

theorem p_dist : (CFSG.KC.HNFSub.allKeys CFSG.KD.HNFSub.S7.segs).length = 88704 ∧
    (CFSG.KC.HNFSub.allKeys CFSG.KD.HNFSub.S7.segs).Nodup :=
  distOK_sound CFSG.KD.HNFSub.dist

theorem p_keys : ∀ Q : Set (Submodule (ZMod 5) V), spanR CFSG.KD.HNFSub.S7.r0 ∈ Q →
    (∀ W ∈ Q, W.map (Matrix.vecMulLinear (MW RA RB BI (invW hnfW1))) ∈ Q ∧
      W.map (Matrix.vecMulLinear (MW RA RB BI (invW hnfW2))) ∈ Q) →
    ∀ k ∈ CFSG.KC.HNFSub.allKeys CFSG.KD.HNFSub.S7.segs, KeyReal CFSG.KD.HNFSub.S7.cols Q k := by
  obtain ⟨hr0, -⟩ := base_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.base
  intro Q hB hQ k hk
  obtain ⟨i, hi, hki⟩ := mem_allKeys _ k hk
  rw [segs_length] at hi
  exact seg_sound CFSG.KD.FamHNSeed.consts cA cB cBi' (segsOK i hi) hr0 Q hB hQ k hki

theorem p_us : ∀ s ∈ CFSG.KD.HNFSub.F7.us, ∃ c ∈ hnfC0,
    ρJ c = MS RA RB BI hnfW1 hnfW2 (decW s) ∧ ρJ c⁻¹ = MS RA RB BI hnfW1 hnfW2 (invW (decW s)) := by
  obtain ⟨hr0, -⟩ := base_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.base
  obtain ⟨-, -, vus, -⟩ := fibU_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.fib hr0
  exact fun s hs => ⟨wordProd hnfGen (decW s), mem_C0 (vus s hs), ρ_stab _ (vus s hs),
    ρ_gen_inv (vus s hs)⟩

theorem p_fix : ∀ s ∈ CFSG.KD.HNFSub.F7.us, spanR CFSG.KD.HNFSub.S7.r0 ≤
    (spanR CFSG.KD.HNFSub.S7.r0).map (Matrix.vecMulLinear (MS RA RB BI hnfW1 hnfW2 (decW s))) := by
  obtain ⟨hr0, -⟩ := base_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.base
  obtain ⟨-, -, -, hfix, -⟩ := fibU_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.fib hr0
  exact hfix

theorem p_N (K : Subgroup ↥JH) (hK : ∀ s ∈ CFSG.KD.HNFSub.F7.us, ∃ k ∈ K,
    ρJ k = MS RA RB BI hnfW1 hnfW2 (decW s) ∧ ρJ k⁻¹ = MS RA RB BI hnfW1 hnfW2 (invW (decW s))) :
    4 ≤ (conjS K β7).ncard := by
  have hfin : Finite ↥JH := Finite.of_injective ρJ ρJ_injective
  obtain ⟨hr0, -⟩ := base_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.base
  obtain ⟨-, -, -, -, hN⟩ := fibU_sound CFSG.KD.FamHNSeed.consts cA cB cBi' CFSG.KD.HNFSub.fib hr0
  exact hN ρJ K _ (ρ_rep (i := 7) (by norm_num)) hK

theorem bound7 : 354816 ≤ (conjOrb hnfC0 β7).ncard := by
  have hfin : Finite ↥JH := Finite.of_injective ρJ ρJ_injective
  have h := sub_bound (cols := CFSG.KD.HNFSub.S7.cols) ρJ hnfC0 aJ β7 p_comm p_U p_G0 p_G1
    p_dist.2 p_dist.1 p_keys (fun s => MS RA RB BI hnfW1 hnfW2 (decW s))
    (fun s => MS RA RB BI hnfW1 hnfW2 (invW (decW s))) p_us p_fix p_N
  have e : (354816 : ℕ) = 88704 * 4 := by norm_num
  rw [e]
  exact h

end CertificateChecks.KernelHNFSub

end
