module

public import Certificates.Kernel.Fi24.Chain
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK
public import CFSG.Certificates.Kernel.Fam.Fi24Act.LibSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Fi24.FactsF1
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Fi24.Slices.Bind
import CFSG.Certificates.Kernel.Fi24.Slices.Head1
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.A0
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.A1
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.A2
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L0
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L1
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L2
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L3
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L4
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L5
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L6
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L7
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L8
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L9
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L10
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L11
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L12
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L13
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L14
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L15
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L16
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L17
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L18
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L19
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L20
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L21
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L22
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.L23
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.LJL0
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.LJL1
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.LJL2
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.LJL3
import CFSG.Certificates.Kernel.Fam.Fi24Act.Checks.LJL4
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.LceSP.Cosets

public section

namespace CFSG.KD.FamFi24Act

open CFSG.KC.Fi24Act

#kc_forall_chunks alAll (fun k => aliveEnum CFSG.KD.F1.LVs TA CFSG.KD.F1.nC (nat_lit 306936)
  (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.alC 1
#kc_forall_chunks covAll0 (fun k => covTabL CFSG.KD.F1.blk TA T0 R0 (nat_lit 6653548) (nat_lit 0)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov0C 1
#kc_forall_chunks covAll1 (fun k => covTabL CFSG.KD.F1.blk TA T1 R1 (nat_lit 6653548) (nat_lit 2)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov1C 1
#kc_forall_chunks covAll2 (fun k => covTabL CFSG.KD.F1.blk TA T2 R2 (nat_lit 6653548) (nat_lit 4)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov2C 1
#kc_forall_chunks covAll3 (fun k => covTabL CFSG.KD.F1.blk TA T3 R3 (nat_lit 6653548) (nat_lit 6)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov3C 1
#kc_forall_chunks covAll4 (fun k => covTabL CFSG.KD.F1.blk TA T4 R4 (nat_lit 6653548) (nat_lit 8)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov4C 1
#kc_forall_chunks covAll5 (fun k => covTabL CFSG.KD.F1.blk TA T5 R5 (nat_lit 6653548) (nat_lit 10)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov5C 1
#kc_forall_chunks covAll6 (fun k => covTabL CFSG.KD.F1.blk TA T6 R6 (nat_lit 6653548) (nat_lit 12)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov6C 1
#kc_forall_chunks covAll7 (fun k => covTabL CFSG.KD.F1.blk TA T7 R7 (nat_lit 6653548) (nat_lit 14)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov7C 1
#kc_forall_chunks covAll8 (fun k => covTabL CFSG.KD.F1.blk TA T8 R8 (nat_lit 6653548) (nat_lit 16)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov8C 1
#kc_forall_chunks covAll9 (fun k => covTabL CFSG.KD.F1.blk TA T9 R9 (nat_lit 6653548) (nat_lit 20)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.cov9C 1
#kc_forall_chunks covAllJ (fun k => covTabL CFSG.KD.F1.blk TA TJ RJ (nat_lit 6653548) (nat_lit 18)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.covJC 1
#kc_forall_chunks covAllL (fun k => covTabL CFSG.KD.F1.blk TA TL RL (nat_lit 6653548) (nat_lit 22)
  (nat_lit 306936) (Nat.mul (nat_lit 512) k) (nat_lit 512) = true) 599 CFSG.KD.FamFi24Act.covLC 1

end CFSG.KD.FamFi24Act

namespace CertificateChecks.KernelFi24Fix

open CFSG.KC CFSG.KC.LceS CFSG.KC.Fi24Act CFSG.Certificates CFSG.Certificates.LceP
  CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 TauCeti.Sporadic

noncomputable abbrev H1 : Subgroup Fi24AutomorphismGroup :=
  Subgroup.closure (g0 '' {g | g < 9 ∨ g = 10})

theorem stWords : ∀ j < 10, bv g0 (wWord (CFSG.KD.F1.selST j)) (wLen (CFSG.KD.F1.selST j)) =
    g0 (if j = 9 then 10 else j) := by
  intro j hj
  interval_cases j
  · have e : CFSG.KD.F1.selST 0 = 4 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 0 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 1 = 0x2004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 1 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 2 = 0x4004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 2 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 3 = 0x6004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 3 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 4 = 0x8004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 4 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 5 = 0xa004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 5 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 6 = 0xc004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 6 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 7 = 0xe004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 7 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 8 = 0x10004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 8 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)
  · have e : CFSG.KD.F1.selST 9 = 0x14004 := Nat.eq_of_beq_eq_true (CFSG.KD.FamFi24Act.ST.all 9 (by decide))
    rw [e]
    exact bval_single g0 (by decide) (by decide) (by norm_num)

theorem hH1 : Subgroup.closure ((fun j => bv g0 (wWord (CFSG.KD.F1.selST j))
    (wLen (CFSG.KD.F1.selST j))) '' {j | j < 10}) = H1 := by
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨if j = 9 then 10 else j, ?_, (stWords j hj).symm⟩
    change j < 10 at hj
    change (if j = 9 then 10 else j) < 9 ∨ (if j = 9 then 10 else j) = 10
    split_ifs <;> omega
  · rintro ⟨g, hg, rfl⟩
    rcases hg with hg | rfl
    · exact ⟨g, (by change g < 10; omega), (stWords g (by omega)).trans (by rw [if_neg (by omega)])⟩
    · exact ⟨9, (by change 9 < 10; omega), (stWords 9 (by omega)).trans (by rw [if_pos rfl])⟩

theorem hK1 : Subgroup.closure (g0 '' {g | 2 * g < 24}) = ⊤ := by
  have e : {g : ℕ | 2 * g < 24} = {g | g < 12} := by
    ext g
    change 2 * g < 24 ↔ g < 12
    omega
  rw [e]
  exact closure_pgen _

theorem tab_all (H : Subgroup Fi24AutomorphismGroup) (rep : ℕ → Fi24AutomorphismGroup)
    (hfacts : ∀ e < 6653548,
      rep (fx (fct CFSG.KD.F1.blk e)) * lv g0 (fc (fct CFSG.KD.F1.blk e)) *
        (rep (fy (fct CFSG.KD.F1.blk e)))⁻¹ ∈ H ∧
      rep (fy (fct CFSG.KD.F1.blk e)) * lv g0 (fic (fct CFSG.KD.F1.blk e)) *
        (rep (fx (fct CFSG.KD.F1.blk e)))⁻¹ ∈ H)
    (hA : ∀ i < 306936, CFSG.KD.FamFi24Act.TA i < 1048576) {T Rr : ℕ → ℕ} {c : ℕ} (hc : c < 256)
    (hch : ∀ k < 599, covTabL CFSG.KD.F1.blk CFSG.KD.FamFi24Act.TA T Rr 6653548 c 306936
      (Nat.mul 512 k) 512 = true)
    (hl : covTabL CFSG.KD.F1.blk CFSG.KD.FamFi24Act.TA T Rr 6653548 c 306936 306688 248 = true) :
    ∀ i < 306936, T i < 306936 ∧ rep (CFSG.KD.FamFi24Act.TA i) * lv g0 c *
      (rep (CFSG.KD.FamFi24Act.TA (T i)))⁻¹ ∈ H := by
  intro i hi
  by_cases h : i < 306688
  · have hk : i / 512 < 599 := by omega
    have := Fi24ActS.covTabL_reps g0 H rep hfacts (fun t ht => hA _ (by
      change 512 * (i / 512) + t < 306936
      omega)) hc (hch (i / 512) hk) (i % 512) (Nat.mod_lt _ (by norm_num))
    have e : Nat.mul 512 (i / 512) + i % 512 = i := by
      change 512 * (i / 512) + i % 512 = i
      omega
    rw [e] at this
    exact this
  · have := Fi24ActS.covTabL_reps g0 H rep hfacts (fun t ht => hA _ (by omega)) hc hl (i - 306688)
      (by omega)
    have e : 306688 + (i - 306688) = i := by omega
    rw [e] at this
    exact this

theorem alive_all : ∀ i < 306936, CFSG.KD.FamFi24Act.TA i < 478324 ∧
    alive CFSG.KD.F1.LVs (CFSG.KD.FamFi24Act.TA i) = true ∧
    (i + 1 < 306936 → CFSG.KD.FamFi24Act.TA i < CFSG.KD.FamFi24Act.TA (i + 1)) := by
  have hnC : CFSG.KD.F1.nC = 478324 := Nat.eq_of_beq_eq_true CFSG.KD.F1.sH3
  intro i hi
  by_cases h : i < 306688
  · have hk : i / 512 < 599 := by omega
    obtain ⟨-, h2⟩ := Fi24FixS.aliveEnum_spec (CFSG.KD.FamFi24Act.alAll (i / 512) hk)
    have := h2 (i % 512) (Nat.mod_lt _ (by norm_num))
    have e : Nat.mul 512 (i / 512) + i % 512 = i := by
      change 512 * (i / 512) + i % 512 = i
      omega
    rw [e, hnC] at this
    exact this
  · have hl : aliveEnum CFSG.KD.F1.LVs CFSG.KD.FamFi24Act.TA CFSG.KD.F1.nC 306936 306688 248 =
        true := CFSG.KD.FamFi24Act.alC599
    obtain ⟨-, h2⟩ := Fi24FixS.aliveEnum_spec hl
    have ht : i - 306688 < 248 := by omega
    have := h2 (i - 306688) ht
    have e : 306688 + (i - 306688) = i := by omega
    rw [e, hnC] at this
    exact this

theorem TA_mono : ∀ d i, i + d + 1 < 306936 →
    CFSG.KD.FamFi24Act.TA i < CFSG.KD.FamFi24Act.TA (i + d + 1)
  | 0, i, h => (alive_all i (by omega)).2.2 h
  | d + 1, i, h => lt_trans (TA_mono d i (by omega))
      ((alive_all (i + d + 1) (by omega)).2.2 (by omega))

theorem rankFacts : ∃ R : ℕ → Fi24AutomorphismGroup, R 0 = 1 ∧
    (∀ g < 12, ∀ i < 306936, CFSG.KD.Fi24Fix.TG g i < 306936 ∧
      R i * g0 g * (R (CFSG.KD.Fi24Fix.TG g i))⁻¹ ∈ H1) ∧
    (∀ q, ∃ i < 306936, q * (R i)⁻¹ ∈ H1) := by
  have hF1 := lceOk_intro CFSG.KD.F1.sH1 CFSG.KD.F1.sH0 CFSG.KD.Fi24B.bHF1 CFSG.KD.F1.sH2
    CFSG.KD.F1.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) F1facts (by quickRfl) (by quickRfl) F1cover (by quickRfl)
  obtain ⟨rep, hrep0, -, hfacts, hcov, hcnt⟩ := lceOk_reps hF1 g0 _ _ rfl rfl r1
  rw [hH1] at hfacts hcov
  have hA : ∀ i < 306936, CFSG.KD.FamFi24Act.TA i < 1048576 := fun i hi =>
    lt_trans (alive_all i hi).1 (by norm_num)
  have hT : ∀ {T Rr : ℕ → ℕ} {c : ℕ}, c < 256 →
      (∀ k < 599, covTabL CFSG.KD.F1.blk CFSG.KD.FamFi24Act.TA T Rr 6653548 c 306936
        (Nat.mul 512 k) 512 = true) →
      covTabL CFSG.KD.F1.blk CFSG.KD.FamFi24Act.TA T Rr 6653548 c 306936 306688 248 = true →
      ∀ i < 306936, T i < 306936 ∧ rep (CFSG.KD.FamFi24Act.TA i) * lv g0 c *
        (rep (CFSG.KD.FamFi24Act.TA (T i)))⁻¹ ∈ H1 := fun hc hch hl => tab_all H1 rep (fun e he => (hfacts e he).2.2) hA hc hch hl
  have hta0 : CFSG.KD.FamFi24Act.TA 0 = 0 := Nat.eq_of_beq_eq_true (by quickRfl)
  refine ⟨fun i => rep (CFSG.KD.FamFi24Act.TA i), ?_, ?_, ?_⟩
  · change rep (CFSG.KD.FamFi24Act.TA 0) = 1
    rw [hta0, hrep0]
  · intro g hg i hi
    interval_cases g
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll0 CFSG.KD.FamFi24Act.cov0C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll1 CFSG.KD.FamFi24Act.cov1C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll2 CFSG.KD.FamFi24Act.cov2C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll3 CFSG.KD.FamFi24Act.cov3C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll4 CFSG.KD.FamFi24Act.cov4C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll5 CFSG.KD.FamFi24Act.cov5C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll6 CFSG.KD.FamFi24Act.cov6C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll7 CFSG.KD.FamFi24Act.cov7C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll8 CFSG.KD.FamFi24Act.cov8C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAllJ CFSG.KD.FamFi24Act.covJC599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAll9 CFSG.KD.FamFi24Act.cov9C599 i hi
    · exact hT (by norm_num) CFSG.KD.FamFi24Act.covAllL CFSG.KD.FamFi24Act.covLC599 i hi
  · intro q
    have hq0 : q ∈ Subgroup.closure (g0 '' {g | 2 * g < 24}) := by
      rw [hK1]
      exact Subgroup.mem_top q
    obtain ⟨y, hy, hal, hq⟩ := hcov q hq0
    have hsub : (Finset.range 306936).image CFSG.KD.FamFi24Act.TA ⊆
        (Finset.range CFSG.KD.F1.nC).filter fun y => alive CFSG.KD.F1.LVs y = true := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_range] at hi
      have hnC : CFSG.KD.F1.nC = 478324 := Nat.eq_of_beq_eq_true CFSG.KD.F1.sH3
      rw [Finset.mem_filter, Finset.mem_range, hnC]
      exact ⟨(alive_all i hi).1, (alive_all i hi).2.1⟩
    have hinj : Set.InjOn CFSG.KD.FamFi24Act.TA (Finset.range 306936 : Set ℕ) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := TA_mono (j - i - 1) i (by omega)
        rw [show i + (j - i - 1) + 1 = j by omega] at this
        omega
      · have := TA_mono (i - j - 1) j (by omega)
        rw [show j + (i - j - 1) + 1 = i by omega] at this
        omega
    have hcard : ((Finset.range 306936).image CFSG.KD.FamFi24Act.TA).card = 306936 := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hcnt)
    have hmem : y ∈ (Finset.range CFSG.KD.F1.nC).filter fun y => alive CFSG.KD.F1.LVs y = true :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 hy, hal⟩
    rw [← heq] at hmem
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hmem
    exact ⟨i, Finset.mem_range.1 hi, hq⟩

end CertificateChecks.KernelFi24Fix

end
