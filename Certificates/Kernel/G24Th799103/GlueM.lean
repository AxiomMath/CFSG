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
open scoped Pointwise commutatorElement


noncomputable abbrev gM : Subgroup Pm := twoBD ⊓ Subgroup.centralizer {tau}

theorem pp_xyG : ∀ k < 2, PP 1365 11 (xyG k) := fun k hk => by
  interval_cases k
  · exact pp_rG 0 (by norm_num)
  · exact pp_rG 1 (by norm_num)

theorem mem_xyG : ∀ k < 2, toPerm 1365 11 (xyG k) ∈ twoBD := fun k hk => by
  interval_cases k
  · change toPerm 1365 11 (LC.S 0) ∈ twoBD
    rw [toPerm_x]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · change toPerm 1365 11 (LC.S 1) ∈ twoBD
    rw [toPerm_y]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem card_M_le : Nat.card gM ≤ 12096 := by
  obtain ⟨hp, hl⟩ := band ch799103_mq0
  obtain ⟨hy, h1⟩ := card_stab_le_of_pointOrbK (H := twoBD) pp_xyG mem_xyG hp
  rw [Nat.eq_of_beq_eq_true hl, CFSG.Sporadic.Co1Block.card_twoBD] at h1
  set y0 : Fin 1365 := ⟨Y0, hy⟩
  set D0 := twoBD ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) y0
  obtain ⟨-, hag⟩ := band ch799103_mag
  have hA : ∀ k < 3, PP 1365 11 (aG k) ∧ toPerm 1365 11 (aG k) ∈ D0 := fun k hk => by
    obtain ⟨h12, h3⟩ := band (Orb.allN_iff.1 hag k hk)
    obtain ⟨hpb, hd⟩ := band h12
    have pp := pp_of hpb
    refine ⟨pp, Subgroup.mem_inf.2 ⟨mem_D_of_inDK pp hd,
      MulAction.mem_stabilizer_iff.2 (Fin.ext ?_)⟩⟩
    rw [Equiv.Perm.smul_def, toPerm_apply pp]
    exact Nat.eq_of_beq_eq_true h3
  have h2 := card_stab_le_of_setOrbK (H := D0) (fun k hk => (hA k hk).1) (fun k hk => (hA k hk).2)
    ch799103_mst
  obtain ⟨hm3, hst⟩ := band ch799103_mtm
  obtain ⟨hm2, hpop⟩ := band hm3
  obtain ⟨hfix, hy0⟩ := band hm2
  rw [Nat.eq_of_beq_eq_true hst] at h2
  have hFT := ptsM_fixMK pp_tau hfix
  set S := twoBD ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (ptsM 1365 TM)
  have hMS : gM ≤ S := fun g hg => by
    obtain ⟨hgD, hgc⟩ := Subgroup.mem_inf.1 hg
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hgc
    refine Subgroup.mem_inf.2 ⟨hgD, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [hFT]
    exact smul_fix_eq hc
  have hle : (S ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) y0 : Subgroup Pm) ≤
      D0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (ptsM 1365 TM) := by
    intro g hg
    obtain ⟨hgS, hgy⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgD, hgT⟩ := Subgroup.mem_inf.1 hgS
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgD, hgy⟩, hgT⟩
  have hcard : (Finset.univ.filter fun i : Fin 1365 => Nat.testBit TM i = true).card = 63 := by
    rw [card_filter_testBit]
    exact Nat.eq_of_beq_eq_true hpop
  have hy0' : y0 ∈ ptsM 1365 TM := hy0
  have hmap : ∀ h ∈ S, h y0 ∈ Finset.univ.filter fun i : Fin 1365 => Nat.testBit TM i = true :=
    fun h hh => by
      have hF := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hh).2
      have hm : h • y0 ∈ h • ptsM 1365 TM := Set.smul_mem_smul_set hy0'
      rw [hF] at hm
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩
  have h4 := card_le_of_maps _ hmap
  rw [hcard] at h4
  have hB := (Nat.mul_le_mul_left 960 (Subgroup.card_le_of_le hle)).trans h2
  have hX : Nat.card (S ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) y0 : Subgroup Pm) ≤ 192 := by
    have := (Nat.mul_le_mul_left 1365 hB).trans h1
    omega
  exact (Subgroup.card_le_of_le hMS).trans (h4.trans (Nat.mul_le_mul_left 63 hX))

theorem mG_mem : ∀ k < 2, PP 1365 11 (mG k) ∧ toPerm 1365 11 (mG k) ∈ gM := fun k hk => by
  obtain ⟨h12, h3⟩ := band (Orb.allN_iff.1 ch799103_mmem k hk)
  obtain ⟨hpb, hd⟩ := band h12
  have pp := pp_of hpb
  refine ⟨pp, Subgroup.mem_inf.2 ⟨mem_D_of_inDK pp hd,
    Subgroup.mem_centralizer_singleton_iff.2 ((commPt_iff pp pp_tau).1 h3)⟩⟩

theorem o2_M : ∀ Q : Subgroup Pm, IsPGroup 2 Q → Q ≤ ⁅gM, gM⁆ →
    ⁅gM, gM⁆ ≤ Subgroup.normalizer (Q : Set Pm) → Q = ⊥ := by
  obtain ⟨hn12, hprod⟩ := band ch799103_mn
  obtain ⟨hn, hb⟩ := band hn12
  obtain ⟨e0, e1⟩ := band ch799103_mdg
  have p0 := (mG_mem 0 (by norm_num)).1
  have p1 := (mG_mem 1 (by norm_num)).1
  have m0 := (mG_mem 0 (by norm_num)).2
  have m1 := (mG_mem 1 (by norm_num)).2
  refine eq_bot_of_card_checks (Mg := mG) (Dg := dG) (nm := 2) (x := XO) (m := 12096) (RO := RO)
    (L := NM) (WS := WM) g24sz (Nat.eq_of_beq_eq_true hprod) card_M_le mG_mem hn hb
    (fun k hk => ?_) ch799103_mw ch799103_mo
  interval_cases k
  · exact ⟨mG 0, mG 1, p0, p1, m0, m1, Nat.eq_of_beq_eq_true e0⟩
  · refine ⟨mG 0, mulG (mG 0) (mG 1), p0, p0.mul p1, m0, ?_, Nat.eq_of_beq_eq_true e1⟩
    rw [toPerm_mulG p0 p1]
    exact gM.mul_mem m0 m1

theorem o2_tau : ∀ Q : Subgroup Pm, IsPGroup 2 Q →
    Q ≤ ⁅twoBD ⊓ Subgroup.centralizer {permOfArr 1365 g24ThTau},
      twoBD ⊓ Subgroup.centralizer {permOfArr 1365 g24ThTau}⁆ →
    ⁅twoBD ⊓ Subgroup.centralizer {permOfArr 1365 g24ThTau},
      twoBD ⊓ Subgroup.centralizer {permOfArr 1365 g24ThTau}⁆ ≤
        Subgroup.normalizer (Q : Set Pm) → Q = ⊥ := by
  rw [← tau_eq]
  exact o2_M

theorem basic_facts :
    permOfArr 1365 g24ThC1 ^ 3 = 1 ∧ permOfArr 1365 g24ThC2 ^ 3 = 1 ∧
      permOfArr 1365 g24ThC1 * permOfArr 1365 g24ThC2 =
        permOfArr 1365 g24ThC2 * permOfArr 1365 g24ThC1 ∧
      permOfArr 1365 g24ThC1 ≠ 1 ∧ permOfArr 1365 g24ThC2 ≠ 1 ∧
      permOfArr 1365 g24ThC2 ≠ permOfArr 1365 g24ThC1 ∧
      permOfArr 1365 g24ThC2 ≠ permOfArr 1365 g24ThC1 ^ 2 ∧
      permOfArr 1365 g24ThTau ^ 2 = 1 ∧
      permOfArr 1365 g24ThTau * xBar * (permOfArr 1365 g24ThTau)⁻¹ ∈ twoBD ∧
      permOfArr 1365 g24ThTau * yBar * (permOfArr 1365 g24ThTau)⁻¹ ∈ twoBD ∧
      permOfArr 1365 g24ThTau ∉ twoBD ∧
      permOfArr 1365 g24ThC1 ∈ ⁅twoBD ⊓ Subgroup.centralizer {permOfArr 1365 g24ThTau},
        twoBD ⊓ Subgroup.centralizer {permOfArr 1365 g24ThTau}⁆ ∧
      permOfArr 1365 g24ThC2 ∈ ⁅twoBD ⊓ Subgroup.centralizer {permOfArr 1365 g24ThTau},
        twoBD ⊓ Subgroup.centralizer {permOfArr 1365 g24ThTau}⁆ := by
  have p0 := pp_TG3 0 (by norm_num)
  have p1 := pp_TG3 1 (by norm_num)
  have e0 : permOfArr 1365 g24ThC1 = toPerm 1365 11 (TG.F 0) := (toPerm_TG (by norm_num) p0).symm
  have e1 : permOfArr 1365 g24ThC2 = toPerm 1365 11 (TG.F 1) := (toPerm_TG (by norm_num) p1).symm
  have pid : PP 1365 11 (pidn 1365 11) := PP.id g24sz
  obtain ⟨h7, hc2c1sq⟩ := band ch799103_bc
  obtain ⟨h6, hc2c1⟩ := band h7
  obtain ⟨h5, hc2⟩ := band h6
  obtain ⟨h4, hc1⟩ := band h5
  obtain ⟨h3, hcomm⟩ := band h4
  obtain ⟨hcub1, hcub2⟩ := band h3
  obtain ⟨hw12, hw3⟩ := band ch799103_bw
  obtain ⟨hw, hw2⟩ := band hw12
  have hW : ∀ k < 4, PP 1365 11 (wT k) ∧ toPerm 1365 11 (wT k) ∈ gM := fun k hk => by
    obtain ⟨h12, h3⟩ := band (Orb.allN_iff.1 hw k hk)
    obtain ⟨hpb, hd⟩ := band h12
    have pp := pp_of hpb
    exact ⟨pp, Subgroup.mem_inf.2 ⟨mem_D_of_inDK pp hd,
      Subgroup.mem_centralizer_singleton_iff.2 ((commPt_iff pp pp_tau).1 h3)⟩⟩
  have hc1M : toPerm 1365 11 (TG.F 0) ∈ ⁅gM, gM⁆ := by
    rw [← eq_of_beq hw2, toPerm_commP (hW 0 (by norm_num)).1 (hW 1 (by norm_num)).1]
    exact Subgroup.commutator_mem_commutator (hW 0 (by norm_num)).2 (hW 1 (by norm_num)).2
  have hc2M : toPerm 1365 11 (TG.F 1) ∈ ⁅gM, gM⁆ := by
    rw [← eq_of_beq hw3, toPerm_commP (hW 2 (by norm_num)).1 (hW 3 (by norm_num)).1]
    exact Subgroup.commutator_mem_commutator (hW 2 (by norm_num)).2 (hW 3 (by norm_num)).2
  rw [e0, e1, ← tau_eq, tau_inv]
  refine ⟨cube_of_cubePt p0 hcub1, cube_of_cubePt p1 hcub2, (commPt_iff p0 p1).1 hcomm, ?_, ?_,
    ne_of_beq p1 p0 hc2c1, ?_, tau_sq, tau_parts.2.1, tau_parts.2.2, tau_not_mem, hc1M, hc2M⟩
  · rw [← toPerm_one]
    exact ne_of_beq p0 pid hc1
  · rw [← toPerm_one]
    exact ne_of_beq p1 pid hc2
  · have h := ne_of_beq p1 (p0.mul p0) hc2c1sq
    rw [toPerm_mul p0 p0] at h
    rw [pow_two]
    exact h

end CertificateChecks.KernelG24Th

end
