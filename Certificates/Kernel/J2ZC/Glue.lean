module

public import CFSG.Certificates.Kernel.Enum.ZCGlue
public import Certificates.Kernel.J2ZC.Gens
public import Certificates.Kernel.J2ZC.Bind
public import Certificates.Kernel.J2ZC.L0
public import Certificates.Kernel.J2ZC.L1
public import Certificates.Kernel.J2ZC.L2
public import Certificates.Kernel.J2ZC.L3
public import Certificates.Kernel.J2ZC.L4
public import Certificates.Kernel.J2ZC.L5
public import Certificates.Kernel.J2ZC.L6
public import Certificates.Kernel.J2ZC.L7
public import Certificates.Kernel.J2ZC.L8
public import Certificates.Kernel.J2ZC.S
public import CFSG.Sporadic.Schreier.PairJ2Faithful
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZC
public import CFSG.Certificates.Kernel.Enum.SSound

public section

namespace CertificateChecks.J2ZCK

open CFSG.KC.Enum CFSG.KC.EnumSound CFSG.KD.J2ZC CFSG.KS CFSG.KS.Raw.Orb
  CertificateChecks.KernelSpor CFSG.Sporadic.Schreier
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem pm_mask : PM = mask (315 * 9) := Nat.eq_of_beq_eq_true pm_eq

theorem gen_prep : PRep 315 9 A (j2Gen 0) ∧ PRep 315 9 AI (j2Gen 0)⁻¹ ∧
    PRep 315 9 B (j2Gen 1) ∧ PRep 315 9 BI (j2Gen 1)⁻¹ := by
  have h0 := prep_PS J2PC.bindsP J2PC.permP (j := 0) (by norm_num)
  have h1 := prep_PS J2PC.bindsP J2PC.permP (j := 1) (by norm_num)
  rw [Nat.eq_of_beq_eq_true a_eq, Nat.eq_of_beq_eq_true ai_eq, Nat.eq_of_beq_eq_true b_eq,
    Nat.eq_of_beq_eq_true bi_eq]
  exact ⟨h0.1, h0.2, h1.1, h1.2⟩

theorem lChk_all : ∀ i < NL, lChk OT 0 0 0 RO 315 9 (mask 9) 2835 (mask (315 * 9)) 12 4095 NL
    A AI B BI i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true nL_eq] at hi
  rw [← pm_mask]
  have hc : ∀ c < 9, ∀ r < 315, lChk OT 0 0 0 RO 315 9 (mask 9) 2835 PM 12 4095 NL A AI B BI
      (315 * c + r) = true := by
    intro c hc r hr
    interval_cases c
    · exact lRange_iff.1 l0 r hr
    · exact lRange_iff.1 l1 r hr
    · exact lRange_iff.1 l2 r hr
    · exact lRange_iff.1 l3 r hr
    · exact lRange_iff.1 l4 r hr
    · exact lRange_iff.1 l5 r hr
    · exact lRange_iff.1 l6 r hr
    · exact lRange_iff.1 l7 r hr
    · exact lRange_iff.1 l8 r hr
  have h := hc (i / 315) (by omega) (i % 315) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem zChk_all : ∀ i < NL, zChk OT 0 0 0 RO 315 9 (mask 9) 2835 (mask (315 * 9)) 12 4095 NL
    zP zPI 3 i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true nL_eq] at hi
  rw [← pm_mask]
  have hc : ∀ c < 9, ∀ r < 315, zChk OT 0 0 0 RO 315 9 (mask 9) 2835 PM 12 4095 NL zP zPI 3
      (315 * c + r) = true := by
    intro c hc r hr
    interval_cases c
    · exact zRange_iff.1 z0 r hr
    · exact zRange_iff.1 z1 r hr
    · exact zRange_iff.1 z2 r hr
    · exact zRange_iff.1 z3 r hr
    · exact zRange_iff.1 z4 r hr
    · exact zRange_iff.1 z5 r hr
    · exact zRange_iff.1 z6 r hr
    · exact zRange_iff.1 z7 r hr
    · exact zRange_iff.1 z8 r hr
  have h := hc (i / 315) (by omega) (i % 315) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem sChk_all : ∀ i < NS, sChk ET 0 0 0 RE 315 9 (mask 9) 2835 (mask (315 * 9)) 12 4095 NS
    IDN gS 3 true OT 0 0 0 RO NL false 0 (fun _ => 0) 0 (fun _ => 0) 0 i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true nS_eq] at hi
  rw [← pm_mask]
  have h := sRange_iff.1 s0 i hi
  rwa [Nat.zero_add] at h

theorem orderOf_gen01 :
    orderOf (j2Gen 0 * j2Gen 1) = 7 := by
  have e : ((j2PermEquiv (j2SeedA * j2SeedB) : ↥j2P) : Equiv.Perm (Fin 315)) =
      j2Gen 0 * j2Gen 1 := by
    rw [map_mul, Subgroup.coe_mul, j2PermEquiv_seedA, j2PermEquiv_seedB]
  rw [← e, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, j2SeedA, j2SeedB, ← map_mul,
    MulEquiv.orderOf_eq]
  exact CFSG.Sporadic.J2.orderOf_ab

theorem zcw_j2P :
    ZCW ↥j2P 7 := by
  obtain ⟨ha, hai, hb, hbi⟩ := gen_prep
  obtain ⟨U, hU, hUc⟩ := lList_prep lChk_all ha hai hb hbi
  have hz : PRep 315 9 (zP 1) (j2Gen 0 * j2Gen 1) := eq2_prep z_ab ha hb
  have hZ := zPowOK_prep z_pow hz
  have hW : ∀ i < NL, ∃ e : Nat, ∃ j < NL, U j = (j2Gen 0 * j2Gen 1) ^ e * U i *
      ((j2Gen 0 * j2Gen 1) ^ e)⁻¹ ∧ U i * U j ≠ U j * U i := by
    intro i hi
    obtain ⟨e, -, -, j, hj, h1, h2⟩ := zChk_prep (zChk_all i hi) (fun j hj => (hU j hj).1) hi hZ
    exact ⟨e, j, hj, h1, h2⟩
  have hgens : ∀ j, ∃ g : Equiv.Perm (Fin 315), j < 3 → PRep 315 9 (gS j) g ∧ g ∈ j2P := by
    intro j
    by_cases hj : j < 3
    · have he := Nat.eq_of_beq_eq_true (PK.allN_iff.1 syl_gens j hj)
      obtain ⟨g, hg, hp⟩ := wperm_prep (W := wS j) (len := lS j) (by norm_num) (by norm_num)
        ha hai hb hbi
      refine ⟨g, fun _ => ⟨?_, hg⟩⟩
      rw [he]
      exact hp
    · exact ⟨1, fun h => absurd h hj⟩
  choose gG hgG using hgens
  have hid : PRep 315 9 IDN 1 := by
    rw [Nat.eq_of_beq_eq_true idn_eq]
    exact prep_pidn (by norm_num) (by norm_num)
  obtain ⟨Ev, hEv, hmul, hinj, hinv⟩ := sList_prep sChk_all (by norm_num) hid
    (fun j hj => (hgG j hj).1)
  have hcard : Nat.card ↥j2P = 604800 :=
    (Nat.card_congr j2PermEquiv.toEquiv).symm.trans CFSG.Sporadic.J2.card_J2
  have hk : ¬ 2 ^ (7 + 1) ∣ Nat.card ↥j2P := by
    rw [hcard]
    norm_num
  exact zcw_of_lists (ga := j2Gen 0) (gb := j2Gen 1) (k := 7) hk
    (Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    orderOf_gen01 (fun i hi => (hUc i hi).1) (fun i hi => (hUc i hi).2) hW
    (fun j hj => (hgG j hj).2) (Nat.eq_of_beq_eq_true nS_eq) (fun i hi => (hEv i hi).2) hmul
    hinj (hinv rfl U fun ix hix => (hU ix hix).1)

theorem zcw_J2_kernel :
    ZCW CFSG.Blueprint.NativeSporadic.J2 7 :=
  ZCW.of_mulEquiv j2PermEquiv.symm zcw_j2P

end CertificateChecks.J2ZCK

end
