module

public import CFSG.Certificates.Kernel.Enum.ZCHGlue
public import CFSG.Certificates.Kernel.Enum.ZCHSound
public import CFSG.Certificates.Kernel.Enum.ZChkISound
public import Certificates.Kernel.HSZC.Gens
public import Certificates.Kernel.HSZC.Bind
public import Certificates.Kernel.HSZC.L0
public import Certificates.Kernel.HSZC.L1
public import Certificates.Kernel.HSZC.L2
public import Certificates.Kernel.HSZC.L3
public import Certificates.Kernel.HSZC.L4
public import Certificates.Kernel.HSZC.L5
public import Certificates.Kernel.HSZC.L6
public import Certificates.Kernel.HSZC.L7
public import Certificates.Kernel.HSZC.L8
public import Certificates.Kernel.HSZC.L9
public import Certificates.Kernel.HSZC.L10
public import Certificates.Kernel.HSZC.W0
public import Certificates.Kernel.HSZC.W1
public import Certificates.Kernel.HSZC.W2
public import Certificates.Kernel.HSZC.W3
public import Certificates.Kernel.HSZC.W4
public import Certificates.Kernel.HSZC.W5
public import Certificates.Kernel.HSZC.W6
public import Certificates.Kernel.HSZC.S
public import Certificates.Kernel.HSZC.V
public import Certificates.Kernel.HSZC.H
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCHSV
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZC
public import CFSG.Certificates.Kernel.Enum.SSound

public section

namespace CertificateChecks.HSZCK

open CFSG.KC.Enum CFSG.KC.EnumSound CFSG.KD.HSZC CFSG.KS CFSG.KS.Raw.Orb
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem pm_mask : PM = mask (100 * 7) := Nat.eq_of_beq_eq_true pm_eq

theorem lChk_all : ∀ i < NL, lChk OT 0 0 0 RO 100 7 (mask 7) 700 (mask (100 * 7)) 15 32767 NL
    A AI B BI i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true nL_eq] at hi
  rw [← pm_mask]
  have hc : ∀ c < 11, ∀ r < 1925, lChk OT 0 0 0 RO 100 7 (mask 7) 700 PM 15 32767 NL A AI B BI
      (1925 * c + r) = true := by
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
    · exact lRange_iff.1 l9 r hr
    · exact lRange_iff.1 l10 r hr
  have h := hc (i / 1925) (by omega) (i % 1925) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem zChkI_all : ∀ i < NX, zChkI OT 0 0 0 RO 100 7 (mask 7) 700 (mask (100 * 7)) 15 32767
    ZW ZL 8 i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true nX_eq] at hi
  rw [← pm_mask]
  have hc : ∀ c < 7, ∀ r < 3023, zChkI OT 0 0 0 RO 100 7 (mask 7) 700 PM 15 32767 ZW ZL 8
      (3023 * c + r) = true := by
    intro c hc r hr
    interval_cases c
    · exact zRangeI_iff.1 w0 r hr
    · exact zRangeI_iff.1 w1 r hr
    · exact zRangeI_iff.1 w2 r hr
    · exact zRangeI_iff.1 w3 r hr
    · exact zRangeI_iff.1 w4 r hr
    · exact zRangeI_iff.1 w5 r hr
    · exact zRangeI_iff.1 w6 r hr
  have h := hc (i / 3023) (by omega) (i % 3023) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem sChk_all : ∀ i < NS, sChk ET 0 0 0 RE 100 7 (mask 7) 700 (mask (100 * 7)) 15 32767 NS
    IDN gS 3 true OT 0 0 0 RO NL false 0 (fun _ => 0) 0 (fun _ => 0) 0 i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true nS_eq] at hi
  rw [← pm_mask]
  have h := sRange_iff.1 s0 i hi
  rwa [Nat.zero_add] at h

theorem conj_z_step {G : Type} [Group G] {z u : G} (hz : z ^ 7 = 1) :
    ∀ e < 7, ∃ f < 7, z * (z ^ e * u * (z ^ e)⁻¹) * z⁻¹ = z ^ f * u * (z ^ f)⁻¹ := by
  intro e he
  have h1 : z * (z ^ e * u * (z ^ e)⁻¹) * z⁻¹ = z ^ (e + 1) * u * (z ^ (e + 1))⁻¹ := by
    rw [pow_succ']
    group
  by_cases h6 : e + 1 < 7
  · exact ⟨e + 1, h6, h1⟩
  · refine ⟨0, by norm_num, ?_⟩
    have : e + 1 = 7 := by omega
    rw [h1, this, hz]
    simp

theorem zcw_hsV :
    ZCW ↥(Subgroup.closure ({hsVa, hsVb} : Set (Equiv.Perm (Fin 100)))) 7 := by
  have ha := a_prep
  have hai := ai_prep
  have hb := b_prep
  have hbi := bi_prep
  have hid : PRep 100 7 IDN 1 := by
    rw [Nat.eq_of_beq_eq_true idn_eq]
    exact prep_pidn (by norm_num) (by norm_num)
  obtain ⟨U, hU, hUc⟩ := lList_prep lChk_all ha hai hb hbi
  obtain ⟨gz, hgzM, hgz0⟩ := wperm_prep (W := ZW) (len := ZL) (by norm_num) (by norm_num)
    ha hai hb hbi
  have hgz : PRep 100 7 (zP 1) gz := by
    rw [Nat.eq_of_beq_eq_true z_word]
    exact hgz0
  have hgzw : wG hsVa hsVb ZW ZL = gz := CFSG.KC.EnumSound.prep_unique (wperm_prep_word (ai := AI) (bi := BI)
    (by norm_num) (by norm_num) ha hb fun k hk => Nat.blt_eq.mp (PK.allN_iff.1 z_letters k hk))
    hgz0
  obtain ⟨g2, hg2M, hg20⟩ := wperm_prep (W := H2W) (len := H2L) (by norm_num) (by norm_num)
    ha hai hb hbi
  have hg2 : PRep 100 7 H2 g2 := by
    rw [Nat.eq_of_beq_eq_true h2_word]
    exact hg20
  have hZ := zPowOK_prep z_pow hgz
  have hz7 : gz ^ 7 = 1 := by
    have h := (hZ 7 (by norm_num)).1
    rw [Nat.eq_of_beq_eq_true z_seven] at h
    exact CFSG.KC.EnumSound.prep_unique h hid
  have hz1 : gz ≠ 1 := ne_one_of_moves z_ne (Nat.blt_eq.mp zp_lt) hgz
  have hzo : orderOf gz = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hz7 hz1
  have hg22 : g2 * g2 = 1 := CFSG.KC.EnumSound.prep_unique (eq2_prep h2_sq hg2 hg2) hid
  have hg2i : PRep 100 7 H2 g2⁻¹ := by
    rw [inv_eq_of_mul_eq_one_left hg22]
    exact hg2
  have hNH := Nat.eq_of_beq_eq_true nH_eq
  obtain ⟨s, hs, hsimp, hncomm, hsH⟩ := hList_simple (n := 100) (w := 7) (iw := 0) (T := HT)
    (sh := 0) (lm := 0) (rb := 0) (rm := RH) (nw := 700) (nH := NH) (idn := IDN) (h1 := zP 1)
    (h2 := H2) (nR := 5) (REP := rep) (o1 := 7) (o2 := 2)
    (NC1 := fun i => List.getD NC1 i []) (NC2 := fun i => List.getD NC2 i [])
    (fun k hk => by
      rw [← pm_mask]
      exact hRange_iff.1 h_enum k (by rw [← hNH]; exact hk))
    (by rw [hNH]; norm_num) hid hgz hg2 (by norm_num) (by norm_num) hz7
    (by rw [pow_two]; exact hg22) (by norm_num)
    (fun i hi => Nat.blt_eq.mp (PK.allN_iff.1 h_reps i hi))
    (fun i hi => by rw [← pm_mask]; exact PK.allN_iff.1 h_nc1 i hi)
    (fun i hi => by rw [← pm_mask]; exact PK.allN_iff.1 h_nc2 i hi)
    (ne_comm_of_eq22 z_h2 hgz hg2)
  have hk3 : bAnd(Nat.blt K3 NH, Nat.blt K3P 100) = true := h_k3_lt
  simp only [PK.bAnd_eq, Bool.and_eq_true] at hk3
  have hK3 := Nat.blt_eq.mp hk3.1
  have hK3P := Nat.blt_eq.mp hk3.2
  have hsk := hs K3 hK3
  rw [← pm_mask] at hsk
  have h3 : 3 ∣ Nat.card ↥(Subgroup.closure ({gz, g2} : Set (Equiv.Perm (Fin 100)))) := by
    have hc : s K3 * s K3 * s K3 = 1 := (CFSG.KC.EnumSound.prep_unique (eq3_prep h_k3 hsk hsk hsk) hid)
    have hne : s K3 ≠ 1 := ne_one_of_moves h_k3_ne hK3P hsk
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    refine three_dvd_card_of_orderOf_three (hsH K3 hK3) (orderOf_eq_prime ?_ hne)
    rw [pow_succ, pow_two]
    exact hc
  have hW : ∀ i < NL, (∃ e : Nat, ∃ j < NL, U j = gz ^ e * U i * (gz ^ e)⁻¹ ∧
      U i * U j ≠ U j * U i) ∨
      ∀ g ∈ ({gz, g2} : Set (Equiv.Perm (Fin 100))), ∀ e < 7, ∃ f < 7,
        g * (gz ^ e * U i * (gz ^ e)⁻¹) * g⁻¹ = gz ^ f * U i * (gz ^ f)⁻¹ := by
    intro i hi
    by_cases hx : i < NX
    · left
      obtain ⟨e, -, -, j, hj, h1, h2⟩ := zChkI_prep (zChkI_all i hx) lChk_all
        (fun j hj => (hU j hj).1) ha hai hb hbi hi
      rw [hgzw] at h1
      exact ⟨e, j, hj, h1, h2⟩
    · right
      rw [Nat.eq_of_beq_eq_true nX_eq] at hx
      rw [Nat.eq_of_beq_eq_true nL_eq] at hi
      rintro g (rfl | hg)
      · exact conj_z_step hz7
      · rw [Set.mem_singleton_iff.mp hg]
        have hv := vRange_iff.1 v0 (i - 21161) (by omega)
        rw [show 21161 + (i - 21161) = i by omega] at hv
        have hUi := (hU i (by rw [Nat.eq_of_beq_eq_true nL_eq]; omega)).1
        rw [pm_mask] at hv
        exact vChk_prep hv hUi (fun e he => hZ e (by omega)) hg2 hg2i
  have hgens : ∀ j, ∃ g : Equiv.Perm (Fin 100), j < 3 → PRep 100 7 (gS j) g ∧
      g ∈ Subgroup.closure ({hsVa, hsVb} : Set (Equiv.Perm (Fin 100))) := by
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
  obtain ⟨Ev, hEv, hmul, hinj, hinv⟩ := sList_prep sChk_all (by norm_num) hid
    (fun j hj => (hgG j hj).1)
  have hk : ¬ 2 ^ (9 + 1) ∣ Nat.card ↥(Subgroup.closure ({hsVa, hsVb} :
      Set (Equiv.Perm (Fin 100)))) := by
    rw [card_closure_hsV]
    norm_num
  exact zcw_of_lists_H (k := 9) hk hgzM hzo (fun i hi => (hUc i hi).1) (fun i hi => (hUc i hi).2)
    hgzM hg2M hsimp hncomm (Subgroup.subset_closure (Set.mem_insert _ _)) h3 hW
    (fun j hj => (hgG j hj).2) (Nat.eq_of_beq_eq_true nS_eq) (fun i hi => (hEv i hi).2) hmul
    hinj (hinv rfl U fun ix hix => (hU ix hix).1)

set_option maxHeartbeats 4000000 in
theorem zcw_HS_kernel :
    ZCW CFSG.Blueprint.NativeSporadic.HS 7 :=
  @ZCW.of_mulEquiv _ CFSG.Blueprint.NativeSporadic.HS inferInstance inferInstance closureHsVEquiv 7
    zcw_hsV

end CertificateChecks.HSZCK

end
