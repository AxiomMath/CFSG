module

public import CFSG.Certificates.Kernel.Tower.Search14OSound
public import CFSG.Certificates.Kernel.Tower.CntSound
public import CFSG.Certificates.Kernel.Tower.PcPSound
public import Certificates.Kernel.Tower.WrEPcChecks
public import Certificates.Kernel.Tower.L1Glue
public import Certificates.Kernel.Tower.L3WChecks
public import Certificates.Kernel.Tower.WrETgChecks

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

variable {e : Nat}

theorem ch36408_eord_all (he : e < 12) : ch36408_eord e = true := by
  interval_cases e
  exacts [ch36408_eord0, ch36408_eord1, ch36408_eord2, ch36408_eord3, ch36408_eord4,
    ch36408_eord5, ch36408_eord6, ch36408_eord7, ch36408_eord8, ch36408_eord9, ch36408_eord10,
    ch36408_eord11]

theorem ch36408_elab_all (he : e < 12) : ch36408_elab e = true := by
  interval_cases e
  exacts [ch36408_elab0, ch36408_elab1, ch36408_elab2, ch36408_elab3, ch36408_elab4,
    ch36408_elab5, ch36408_elab6, ch36408_elab7, ch36408_elab8, ch36408_elab9, ch36408_elab10,
    ch36408_elab11]

theorem ch36408_eh_all (he : e < 12) : ch36408_eh e = true := by
  have hU := ch36408_ehU_lt e he
  have hH := ch36408_ehH_all e he
  simp only [ch36408_ehH, Bool.and_eq_true] at hH
  obtain ⟨⟨⟨hH1, hH2⟩, hG⟩, hky⟩ := hH
  have hH1' := allB_true_iff.1 hH1
  have hcnt : cntB 16384 (fun c => Nat.beq (wrEM e c 128) (wrEM e 128 c)) = 256 := by
    refine cntB_of_mask (HL := wrED e 4) (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
      (fun c hc hf => ?_)
    · have h := hH1' j hj
      rw [Bool.and_eq_true] at h
      exact Eq.mp Nat.blt_eq h.1
    · have h := hH1' j hj
      rw [Bool.and_eq_true] at h
      exact h.2
    · exact Eq.mp Nat.blt_eq (allB_true_iff.1 hH2 j (by omega))
    · have h := hU c hc
      rw [wrEhU, Bool.and_eq_true] at h
      have h1 := h.1
      have hf' : Nat.beq (wrEM e c 128) (wrEM e 128 c) = true := hf
      rw [hf'] at h1
      exact h1
  have hOK : hOK16 16384 (wrEM e) 128 (wrED e 4) = true := by
    rw [hOK16, hH1, hH2, hcnt]
    all_goals rfl
  have hT : treeB 16384 4 (wrEM e) (wrED e 5) (wrED e 7) = true := by
    rw [treeB, hG, Bool.true_and, allB_true_iff]
    intro c hc
    have h := hU c hc
    rw [wrEhU, Bool.and_eq_true] at h
    exact h.2
  rw [ch36408_eh, hOK, hT, hky]
  all_goals rfl

theorem ch36408_ecm_all (he : e < 12) : ch36408_ecm e = true := by
  interval_cases e
  exacts [ch36408_ecm0, ch36408_ecm1, ch36408_ecm2, ch36408_ecm3, ch36408_ecm4, ch36408_ecm5,
    ch36408_ecm6, ch36408_ecm7, ch36408_ecm8, ch36408_ecm9, ch36408_ecm10, ch36408_ecm11]

theorem ch36408_el12_all (he : e < 12) : ch36408_el12 e = true := by
  interval_cases e
  exacts [ch36408_el120, ch36408_el121, ch36408_el122, ch36408_el123, ch36408_el124,
    ch36408_el125, ch36408_el126, ch36408_el127, ch36408_el128, ch36408_el129, ch36408_el1210,
    ch36408_el1211]

theorem ch36408_el3_all (he : e < 12) : ch36408_el3 e = true := by
  interval_cases e
  exacts [ch36408_el30, ch36408_el31, ch36408_el32, ch36408_el33, ch36408_el34, ch36408_el35,
    ch36408_el36, ch36408_el37, ch36408_el38, ch36408_el39, ch36408_el310, ch36408_el311]

theorem ch36408_efam_all (he : e < 12) : ch36408_efam e = true := by
  interval_cases e
  exacts [ch36408_efam0, ch36408_efam1, ch36408_efam2, ch36408_efam3, ch36408_efam4,
    ch36408_efam5, ch36408_efam6, ch36408_efam7, ch36408_efam8, ch36408_efam9, ch36408_efam10,
    ch36408_efam11]

theorem ch36408_epc_all (he : e < 12) : ch36408_epc e = true := by
  have h := ch36408_epcP_all e he
  rw [ch36408_epcP] at h
  rw [ch36408_epc]
  exact pcP_pcB (by norm_num) h

theorem ch36408_echi_all (he : e < 12) : ch36408_echi e = true := by
  interval_cases e
  exacts [ch36408_echi0, ch36408_echi1, ch36408_echi2, ch36408_echi3, ch36408_echi4,
    ch36408_echi5, ch36408_echi6, ch36408_echi7, ch36408_echi8, ch36408_echi9, ch36408_echi10,
    ch36408_echi11]

theorem ch36408_epar : allB 12 (fun e => Nat.blt (wrEP e 1) 8192 &&
    Nat.ble (Nat.add (wrEP e 9) (wrEP e 10)) 28) = true := by
  decide +kernel

theorem wrE_par (he : e < 12) : wrEP e 1 < 8192 ∧ wrEP e 9 + wrEP e 10 ≤ 28 := by
  have h := allB_eq_true.1 ch36408_epar e he
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, Nat.le_of_ble_eq_true h.2⟩

theorem wrE_g_lt (he : e < 12) : wrEP e 1 < 8192 := (wrE_par he).1

theorem wrE_fam_le (he : e < 12) : wrEP e 9 + wrEP e 10 ≤ 28 := (wrE_par he).2

theorem wrE_fam (he : e < 12) {k : Nat} (hk : k < wrEP e 10) :
    wrEP e 9 + k < 28 ∧ l16 (l3P (wrEP e 9 + k)) 0 = wrEP e 0 ∧
      l16 (l3P (wrEP e 9 + k)) 1 = wrEP e 1 ∧
        ∀ i < 4, l16 (l3G (wrEP e 9 + k)) i = l16 (wrED e 5) i := by
  have h := allB_eq_true.1 (ch36408_efam_all he) k hk
  simp only [Bool.and_eq_true] at h
  exact ⟨by have := wrE_fam_le he; omega, Nat.eq_of_beq_eq_true h.1.1,
    Nat.eq_of_beq_eq_true h.1.2, fun i hi => Nat.eq_of_beq_eq_true (allB_eq_true.1 h.2 i hi)⟩

variable (E : ExtData (Grp wrS))

theorem wrE_search (he : e < 12)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add (wrEP e 0) 2)) c < 8192 ∧
      E.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add (wrEP e 0) 2)) c))
    (hg : subModel_wr.decW (wrEP e 1) = E.g) (β : MulAut (CycExt E))
    (hβ : β (dec2 E subModel_wr.decW (l16 (wrED e 5) 0)) = dec2 E subModel_wr.decW 128) :
    ∃ h : CycExt E, h * dec2 E subModel_wr.decW 128 = dec2 E subModel_wr.decW 128 * h ∧
      ∃ k < wrEP e 10, ∃ j < 16, ∀ i < 4, h * β (dec2 E subModel_wr.decW (l16 (wrED e 5) i)) * h⁻¹ =
        dec2 E subModel_wr.decW (l16 (l3Im (wrEP e 9 + k) j) i) := by
  have hl := ch36408_elab_all he
  have hh := ch36408_eh_all he
  have hc := ch36408_ecm_all he
  have h12 := ch36408_el12_all he
  simp only [ch36408_elab, ch36408_eh, ch36408_ecm, ch36408_el12, Bool.and_eq_true] at hl hh hc h12
  obtain ⟨h, hht, q, hq, hi⟩ := e14_complete (W2 := fun r1 => wrED e (Nat.add 19 r1))
    (SP := fun r2 => wrED e (Nat.add 19 (Nat.add (wrEP e 6) r2))) rfl
    (tm_model wr_model E hFA (wrE_g_lt he) hg) hh.1.2 (ch36408_eord_all he) hl.1 hl.2 hh.1.1
    hh.2 hc.1.1 hc.1.2 hc.2 h12.1 h12.2 (ch36408_el3_all he)
    (allB_eq_true.1 ch36408_etg_all e he) β hβ
  have hq' : q < 16 * wrEP e 10 := hq
  refine ⟨h, hht, Nat.shiftRight q 4, ?_, Nat.land q 15, ?_, hi⟩
  · have e1 : Nat.shiftRight q 4 = q / 2 ^ 4 := Nat.shiftRight_eq_div_pow q 4
    rw [e1]
    omega
  · have e2 : Nat.land q 15 = q % 2 ^ 4 := Nat.and_two_pow_sub_one_eq_mod q 4
    rw [e2]
    omega

variable {X : Type*} [Group X] {dec : Nat → X}

theorem wrE_l2 (he : e < 12) (M : IsModel (⊤ : Subgroup X) 16384 (wrEM e) dec)
    (hL3 : ∀ D : ExtData X, D.α (dec (l16 (wrED e 5) 0)) = dec 128 →
      Nat.card (Subgroup.centralizer {CycExt.incl D (dec 128)} : Subgroup (CycExt D)) = 2 ^ 8 →
        L3Facts (CycExt D) (CycExt.incl D (dec 128))) : L2Facts X (dec 128) := by
  have hl := ch36408_elab_all he
  have hh := ch36408_eh_all he
  simp only [ch36408_elab, ch36408_eh, Bool.and_eq_true] at hl hh
  have hT : treeB 16384 4 (wrEM e) (wrED e 5) (wrED e 7) = true := hh.1.2
  have hx0 : l16 (wrED e 5) 0 < 16384 := treeB_gen hT (by norm_num)
  have hchi := ch36408_echi_all he
  obtain ⟨hnt, hnx⟩ := not_mem_bitQ M hT hchi (by norm_num) hx0
  exact l2Facts_of_l3 (bitQ M hT hchi) (bitQ_normal M hT hchi)
    (bitQ_index M hT hchi (by norm_num)) hnt hnx
    (pcB_sound M rfl hT (by norm_num) hx0 (ch36408_eord_all he) hl.1 hl.2 (ch36408_epc_all he)) hL3

end Certificates.KernelTower
