module

public import Certificates.Kernel.G24Th799103.GlueBase
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta
open CFSG.Sporadic.Co1Block (twoBD xBar yBar)
open CertificateChecks.KernelG24.Tri27206
open scoped Pointwise

theorem ptsM_EM : ptsM 1365 EM = ptsM 1365 DM \ ptsM 1365 FM := by
  have h := Orb.allN_iff.1 ch799103_gem
  ext i
  have e : Bool.beq (Nat.testBit EM i) (Nat.testBit DM i && !Nat.testBit FM i) = true := h i i.2
  simp only [ptsM, Set.mem_setOf_eq, Set.mem_diff]
  generalize Nat.testBit EM i = a at e ⊢
  generalize Nat.testBit DM i = b at e ⊢
  generalize Nat.testBit FM i = c at e ⊢
  revert e
  cases a <;> cases b <;> cases c <;> decide

theorem ptsM_fix2MK {g h M : Nat} (hg : PP 1365 11 g) (hh : PP 1365 11 h) (hM : fix2MK g h M = true) :
    ptsM 1365 M = {i : Fin 1365 | toPerm 1365 11 g i = i} ∩ {i : Fin 1365 | toPerm 1365 11 h i = i} := by
  unfold fix2MK at hM
  rw [Orb.allN_iff] at hM
  ext i
  have e : Bool.beq (Nat.testBit M i)
      (Nat.beq (pg 11 (mask 11) g i) i && Nat.beq (pg 11 (mask 11) h i) i) = true := hM i i.2
  have b1 : (pg 11 (mask 11) g i = i) ↔ Nat.beq (pg 11 (mask 11) g i) i = true := by rw [Nat.beq_eq]
  have b2 : (pg 11 (mask 11) h i = i) ↔ Nat.beq (pg 11 (mask 11) h i) i = true := by rw [Nat.beq_eq]
  simp only [ptsM, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [← Fin.val_inj, ← Fin.val_inj, toPerm_apply hg, toPerm_apply hh, b1, b2]
  generalize Nat.testBit M i = a at e ⊢
  generalize Nat.beq (pg 11 (mask 11) g i) i = b at e ⊢
  generalize Nat.beq (pg 11 (mask 11) h i) i = c at e ⊢
  revert e
  cases a <;> cases b <;> cases c <;> decide


theorem mem_rG : ∀ k < 3, toPerm 1365 11 (rG k) ∈ gR := fun k hk => by
  interval_cases k
  · change toPerm 1365 11 (LC.S 0) ∈ gR
    rw [toPerm_x]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · change toPerm 1365 11 (LC.S 1) ∈ gR
    rw [toPerm_y]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact tau_mem_R

noncomputable abbrev gH : Subgroup Pm :=
  gR ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (ptsM 1365 DM) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (ptsM 1365 FM)

theorem card_H_le : Nat.card gH ≤ 216 := by
  obtain ⟨hp, hl⟩ := band ch799103_ip0
  obtain ⟨hx, h1⟩ := card_stab_le_of_pointOrbK (H := gR) pp_rG mem_rG hp
  rw [Nat.eq_of_beq_eq_true hl] at h1
  set x0 : Fin 1365 := ⟨X0, hx⟩
  set R0 := gR ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) x0
  obtain ⟨-, hhg⟩ := band ch799103_ihg
  have hH : ∀ k < 3, PP 1365 11 (hG k) ∧ toPerm 1365 11 (hG k) ∈ R0 := fun k hk => by
    obtain ⟨h12, h3⟩ := band (Orb.allN_iff.1 hhg k hk)
    obtain ⟨hpb, hr⟩ := band h12
    have pp := pp_of hpb
    refine ⟨pp, Subgroup.mem_inf.2 ⟨mem_R_of_inRK pp hr,
      MulAction.mem_stabilizer_iff.2 (Fin.ext ?_)⟩⟩
    rw [Equiv.Perm.smul_def, toPerm_apply pp]
    exact Nat.eq_of_beq_eq_true h3
  have h2 := card_stab_le_of_setOrbK (H := R0) (fun k hk => (hH k hk).1) (fun k hk => (hH k hk).2)
    ch799103_isr
  obtain ⟨hinl3, hsf⟩ := band ch799103_inl
  obtain ⟨-, hsr⟩ := band hinl3
  rw [Nat.eq_of_beq_eq_true hsr] at h2
  obtain ⟨-, hkg⟩ := band ch799103_ikg
  have hK : ∀ k < 3, PP 1365 11 (kG k) ∧
      toPerm 1365 11 (kG k) ∈ R0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (ptsM 1365 DM) := fun k hk => by
    obtain ⟨h123, h4⟩ := band (Orb.allN_iff.1 hkg k hk)
    obtain ⟨h12, h3⟩ := band h123
    obtain ⟨hpb, hr⟩ := band h12
    have pp := pp_of hpb
    refine ⟨pp, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mem_R_of_inRK pp hr,
      MulAction.mem_stabilizer_iff.2 (Fin.ext ?_)⟩, MulAction.mem_stabilizer_iff.2 ?_⟩⟩
    · rw [Equiv.Perm.smul_def, toPerm_apply pp]
      exact Nat.eq_of_beq_eq_true h3
    · rw [← ptsM_imgM pp, Nat.eq_of_beq_eq_true h4]
  have h3 := card_stab_le_of_setOrbK (H := R0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (ptsM 1365 DM))
    (fun k hk => (hK k hk).1) (fun k hk => (hK k hk).2) ch799103_isf
  rw [Nat.eq_of_beq_eq_true hsf] at h3
  have hle : (gH ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) x0 : Subgroup Pm) ≤
      R0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (ptsM 1365 DM) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (ptsM 1365 EM) := by
    intro g hg
    obtain ⟨hgH, hgx⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgRD, hgF⟩ := Subgroup.mem_inf.1 hgH
    obtain ⟨hgR, hgD⟩ := Subgroup.mem_inf.1 hgRD
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgR, hgx⟩, hgD⟩, ?_⟩
    rw [MulAction.mem_stabilizer_iff] at hgD hgF ⊢
    rw [ptsM_EM, Set.smul_set_sdiff, hgD, hgF]
  obtain ⟨hm5, hpop⟩ := band ch799103_imask
  obtain ⟨hm4, -⟩ := band hm5
  obtain ⟨hm3, -⟩ := band hm4
  obtain ⟨-, hx0⟩ := band hm3
  have hS : (Finset.univ.filter fun i : Fin 1365 => Nat.testBit FM i = true).card = 6 := by
    rw [card_filter_testBit]
    exact Nat.eq_of_beq_eq_true hpop
  have hx0' : x0 ∈ ptsM 1365 FM := hx0
  have hmap : ∀ h ∈ gH, h x0 ∈ Finset.univ.filter fun i : Fin 1365 => Nat.testBit FM i = true :=
    fun h hh => by
      have hF := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hh).2
      have hm : h • x0 ∈ h • ptsM 1365 FM := Set.smul_mem_smul_set hx0'
      rw [hF] at hm
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩
  have h4 := card_le_of_maps _ hmap
  rw [hS] at h4
  have hB := (Nat.mul_le_mul_left 160 (Subgroup.card_le_of_le hle)).trans h3
  have hC := (Nat.mul_le_mul_left 64 hB).trans h2
  have hf : Nat.card (gH ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) x0 : Subgroup Pm) ≤ 36 := by
    have := (Nat.mul_le_mul_left 1365 hC).trans (h1.trans card_R_le)
    omega
  exact h4.trans (Nat.mul_le_mul_left 6 hf)

theorem nG_mem : ∀ k < 3, PP 1365 11 (nG k) ∧ toPerm 1365 11 (nG k) ∈ gH := fun k hk => by
  obtain ⟨-, hng⟩ := band ch799103_ing
  obtain ⟨h123, h4⟩ := band (Orb.allN_iff.1 hng k hk)
  obtain ⟨h12, h3⟩ := band h123
  obtain ⟨hpb, hr⟩ := band h12
  have pp := pp_of hpb
  refine ⟨pp, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mem_R_of_inRK pp hr,
    MulAction.mem_stabilizer_iff.2 ?_⟩, MulAction.mem_stabilizer_iff.2 ?_⟩⟩
  · rw [← ptsM_imgM pp, Nat.eq_of_beq_eq_true h3]
  · rw [← ptsM_imgM pp, Nat.eq_of_beq_eq_true h4]

theorem mem_NL {h : Pm} (hh : h ∈ gH) : ∃ r ∈ NL, PP 1365 11 r.1 ∧ toPerm 1365 11 r.1 = h := by
  obtain ⟨hinl3, -⟩ := band ch799103_inl
  obtain ⟨hinl2, -⟩ := band hinl3
  obtain ⟨hnl, hlen⟩ := band hinl2
  have pp : ∀ k < 3, PP 1365 11 (nG k) := fun k hk => (nG_mem k hk).1
  have hle : Subgroup.closure (gens 1365 11 nG 3) ≤ gH := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (nG_mem k hk).2
  have hl : NL.length = 216 := Nat.eq_of_beq_eq_true hlen
  have hge := le_card_of_mulRecK g24sz pp hnl
  have heq := Subgroup.eq_of_le_of_card_ge hle (card_H_le.trans (hl ▸ hge))
  exact mem_of_mulRecK g24sz pp hnl (heq ▸ card_H_le.trans hl.ge) h (heq ▸ hh)

theorem invol_eq_tau {u : Pm} (huR : u ∈ gR) (hu2 : u ^ 2 = 1)
    (h1 : u * toPerm 1365 11 (TG.F 0) = toPerm 1365 11 (TG.F 0) * u)
    (h2 : u * toPerm 1365 11 (TG.F 1) = toPerm 1365 11 (TG.F 1) * u) : u = 1 ∨ u = tau := by
  have p0 := pp_TG3 0 (by norm_num)
  have p1 := pp_TG3 1 (by norm_num)
  obtain ⟨hm5, -⟩ := band ch799103_imask
  obtain ⟨hm4, -⟩ := band hm5
  obtain ⟨hm3, -⟩ := band hm4
  obtain ⟨hm2, -⟩ := band hm3
  obtain ⟨hfd, hff⟩ := band hm2
  have hDS := ptsM_fixMK (p0.mul (p1.mul p1)) hfd
  have hFS := ptsM_fix2MK p0 p1 hff
  have hc1 : Commute u (toPerm 1365 11 (TG.F 0)) := h1
  have hc2 : Commute u (toPerm 1365 11 (TG.F 1)) := h2
  have hc : u * toPerm 1365 11 (mulG (TG.F 0) (mulG (TG.F 1) (TG.F 1))) =
      toPerm 1365 11 (mulG (TG.F 0) (mulG (TG.F 1) (TG.F 1))) * u := by
    rw [toPerm_mulG (y := mulG (TG.F 1) (TG.F 1)) p0 (p1.mul p1), toPerm_mulG p1 p1]
    exact (hc1.mul_right (hc2.mul_right hc2)).eq
  have hmem : u ∈ gH := Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨huR,
    MulAction.mem_stabilizer_iff.2 (by rw [hDS]; exact smul_fix_eq hc)⟩,
    MulAction.mem_stabilizer_iff.2 (by rw [hFS, Set.smul_set_inter, smul_fix_eq h1, smul_fix_eq h2])⟩
  obtain ⟨r, hr, hrp, hre⟩ := mem_NL hmem
  have hsc := allL_iff.1 ch799103_iscan r.1 (List.mem_map_of_mem hr)
  unfold invT at hsc
  rw [(commPt_iff hrp p0).2 (by rw [hre]; exact h1), (commPt_iff hrp p1).2 (by rw [hre]; exact h2),
    invPt_of hrp (by rw [hre]; exact hu2)] at hsc
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hsc
  rcases hsc with e | e
  · left
    rw [← hre, Nat.eq_of_beq_eq_true e, toPerm_one]
  · right
    rw [← hre, Nat.eq_of_beq_eq_true e]

theorem invol_eq {u : Pm} (huR : u ∈ Subgroup.closure {xBar, yBar, permOfArr 1365 g24ThTau})
    (hu2 : u ^ 2 = 1) (h1 : u * permOfArr 1365 g24ThC1 = permOfArr 1365 g24ThC1 * u)
    (h2 : u * permOfArr 1365 g24ThC2 = permOfArr 1365 g24ThC2 * u) :
    u = 1 ∨ u = permOfArr 1365 g24ThTau := by
  have e0 := toPerm_TG (k := 0) (by norm_num) (pp_TG3 0 (by norm_num))
  have e1 := toPerm_TG (k := 1) (by norm_num) (pp_TG3 1 (by norm_num))
  rw [← tau_eq] at huR ⊢
  exact invol_eq_tau huR hu2 (by rw [e0]; exact h1) (by rw [e1]; exact h2)

end CertificateChecks.KernelG24Th

end
