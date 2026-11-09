module

public import CFSG.Certificates.Kernel.Tower.Search14OSound
public import CFSG.Certificates.Kernel.Tower.CntSound
public import CFSG.Certificates.Kernel.Tower.PcPSound
public import CFSG.Certificates.Kernel.Tower.WrECentSound
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

theorem wrPi_eq (t : Nat) : wrPi t = 2 * (t / 128) + t % 2 := by
  have e1 : Nat.shiftRight t 7 = t / 128 := by
    change t >>> 7 = t / 128
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land t 1 = t % 2 := Nat.and_one_is_mod t
  rw [wrPi, e1, e2]
  rfl

theorem wrE_sm0 : ∀ s < 128, lane wrSM 7 127 s = s := fun s hs =>
  Nat.eq_of_beq_eq_true (allB_true_iff.1 ch36408_sm0 s hs)

theorem wrT_mono {T m : Nat} (h : allB (Nat.sub m 1) (fun j =>
      Nat.blt (wrPi (l16 T (Nat.succ j))) (wrPi (l16 T (Nat.succ (Nat.succ j))))) = true) :
    ∀ k < m, ∀ j < k, wrPi (l16 T (j + 1)) < wrPi (l16 T (k + 1)) := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj
    have hs : wrPi (l16 T (k + 1)) < wrPi (l16 T (k + 1 + 1)) :=
      Eq.mp Nat.blt_eq (allB_true_iff.1 h k (by change k < m - 1; omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact Nat.lt_trans (ih (by omega) j hj) hs
    · rw [hj]
      exact hs

theorem wrE_cent (he : e < 12) {X : Type*} [Group X] {dec : Nat → X}
    (M : IsModel (⊤ : Subgroup X) 16384 (wrEM e) dec) {l : Nat} (hl : l < wrEP e 2)
    (hr : l16 (wrED e 2) l < 16384) (hcz : czOK16 16384 (wrED e 1) (wrED e 3) = true) :
    16384 ≤ Nat.card (Subgroup.centralizer {dec (l16 (wrED e 2) l)} : Subgroup X) *
      cntB 16384 (fun c => Nat.beq (lbL (wrED e 1) c) l) := by
  classical
  have h := ch36408_ct_lt e he hl
  rw [wrCtB, wrCtR, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [← cls16_cz (n := 16384) (by norm_num) hcz l]
  have hmono := wrT_mono h3
  have hT : ∀ j < l16 (wrTT e l) 0, l16 (wrTT e l) (j + 1) < 16384 ∧
      wrEM e (l16 (wrTT e l) (j + 1)) (l16 (wrED e 2) l) =
        wrEM e (l16 (wrED e 2) l) (l16 (wrTT e l) (j + 1)) := fun j hj => by
    have h := allB_true_iff.1 h2 j hj
    simp only [Bool.and_eq_true] at h
    exact ⟨Eq.mp Nat.blt_eq h.1, Nat.eq_of_beq_eq_true h.2⟩
  have hne : ∀ j < l16 (wrTT e l) 0, ∀ k < l16 (wrTT e l) 0, j ≠ k →
      wrPi (l16 (wrTT e l) (j + 1)) ≠ wrPi (l16 (wrTT e l) (k + 1)) := by
    intro j hj k hk hjk
    rcases Nat.lt_or_gt_of_ne hjk with hlt | hlt
    · exact Nat.ne_of_lt (hmono k hk j hlt)
    · exact Nat.ne_of_gt (hmono j hj k hlt)
  let A := ((Finset.range 64).filter fun v =>
    Nat.beq (wrEM e (Nat.mul 2 v) (l16 (wrED e 2) l))
      (wrEM e (l16 (wrED e 2) l) (Nat.mul 2 v)) = true).image fun v => 2 * v
  let TT := (Finset.range (l16 (wrTT e l) 0)).image fun j => l16 (wrTT e l) (j + 1)
  have hAc : A.card = cntB 64 (fun v => Nat.beq (wrEM e (Nat.mul 2 v) (l16 (wrED e 2) l))
      (wrEM e (l16 (wrED e 2) l) (Nat.mul 2 v))) := by
    rw [Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left (by norm_num) hab), cntB_eq_card]
  have hTc : TT.card = l16 (wrTT e l) 0 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j hj k hk hjk
    by_contra hc
    rw [Finset.coe_range, Set.mem_Iio] at hj hk
    exact hne j hj k hk hc (congrArg wrPi hjk)
  have hle := cent16_card_ge M wrPi A TT ?_ ?_ ?_ ?_ hr
  · rw [hAc, hTc] at hle
    exact le_trans (Nat.le_of_ble_eq_true h1) (Nat.mul_le_mul_right _ hle)
  · intro a ha
    simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨v, ⟨hv, hc⟩, rfl⟩ := ha
    exact ⟨by omega, Nat.eq_of_beq_eq_true hc⟩
  · intro t ht
    simp only [TT, Finset.mem_image, Finset.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    exact hT j hj
  · intro a ha b hb hab
    simp only [TT, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at ha hb
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := hb
    by_cases hjk : j = k
    · rw [hjk]
    · exact absurd hab (hne j hj k hk hjk)
  · intro a ha t ht
    simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨v, ⟨hv, -⟩, rfl⟩ := ha
    simp only [TT, Finset.mem_image, Finset.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    have hp := tm_wm_pi (SM := wrSM) (AC := wrAC) (FA := wrA (Nat.add (wrEP e 0) 2))
      (g := wrEP e 1) wrE_sm0 hv (hT j hj).1
    have e1 : wrEM e (2 * v) (l16 (wrTT e l) (j + 1)) = tm (wm wrSM wrAC)
        (wrA (Nat.add (wrEP e 0) 2)) (wrEP e 1) (2 * v) (l16 (wrTT e l) (j + 1)) := rfl
    rw [wrPi_eq, wrPi_eq, e1, hp.1, hp.2]

theorem ch36408_elab_all (he : e < 12) {X : Type*} [Group X] {dec : Nat → X}
    (M : IsModel (⊤ : Subgroup X) 16384 (wrEM e) dec) : ch36408_elab e = true := by
  have hH := ch36408_elabH_all e he
  rw [ch36408_elabH, Bool.and_eq_true, Bool.and_eq_true] at hH
  obtain ⟨⟨hGI, hRP⟩, hcz⟩ := hH
  have hG := ch36408_ehH_all e he
  simp only [ch36408_ehH, Bool.and_eq_true] at hG
  have hGS : ∀ i < 4, l16 (wrED e 5) i < 16384 := fun i hi =>
    Eq.mp Nat.blt_eq (allB_true_iff.1 hG.1.2 i hi)
  have hU := ch36408_lt_lt e he
  have hT : ∀ c < 16384, lbG16 (wrED e 1) c < 4 →
      lbL (wrED e 1) (wrEM e (wrEM e (l16 (wrED e 5) (lbG16 (wrED e 1) c)) c)
          (l16 (wrED e 6) (lbG16 (wrED e 1) c))) = lbL (wrED e 1) c ∧
        lbD16 (wrED e 1) (wrEM e (wrEM e (l16 (wrED e 5) (lbG16 (wrED e 1) c)) c)
          (l16 (wrED e 6) (lbG16 (wrED e 1) c))) < lbD16 (wrED e 1) c := fun c hc hg => by
    have h := (ch36408_and_l (hU c hc)).2
    have hg' : Nat.blt (lbG16 (wrED e 1) c) 4 = true := Nat.blt_eq.mpr hg
    rw [wrLtT, hg'] at h
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1, Eq.mp Nat.blt_eq h.2⟩
  have hRl : ∀ l < wrEP e 2, l16 (wrED e 2) l < 16384 := fun l hl => by
    have h := allB_true_iff.1 hRP l hl
    rw [Bool.and_eq_true] at h
    exact Eq.mp Nat.blt_eq h.1
  rw [ch36408_elab, Bool.and_eq_true]
  exact ⟨labOK16_of_cent M hGI hRP hGS (fun c hc => (ch36408_and_l (hU c hc)).1) hT
    fun l hl => wrE_cent he M hl (hRl l hl) hcz, hcz⟩

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

theorem wrE_bit (he : e < 12) {x y : Nat} (hx : x < 16384) (hy : y < 16384) :
    bit (wrX e) (wrEM e x y) = Nat.xor (bit (wrX e) x) (bit (wrX e) y) := by
  have hS := ch36408_echS_all e he
  rw [ch36408_echS, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hS
  obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hg⟩, hD⟩ := hS
  have hs : ∀ c k, Nat.shiftRight c k = c / 2 ^ k := fun c k => Nat.shiftRight_eq_div_pow c k
  refine tm_bit (SM := wrSM) (AC := wrAC) (FA := wrA (Nat.add (wrEP e 0) 2)) (g := wrEP e 1)
    (fun c hc => ?_) (fun s hs t ht => ?_) (fun y hy => ?_) (Eq.mp Nat.blt_eq hg) ?_ hx hy
  · have h := Nat.eq_of_beq_eq_true (allB_true_iff.1 hA c hc)
    have e2 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
    rw [hs, e2] at h
    exact h
  · exact Nat.eq_of_beq_eq_true (allB_true_iff.1 (allB_true_iff.1 hB s hs) t ht)
  · have h := allB_true_iff.1 hC y hy
    rw [Bool.and_eq_true, hs, hs] at h
    exact ⟨Eq.mp Nat.blt_eq h.1, Nat.eq_of_beq_eq_true h.2⟩
  · have h := Nat.eq_of_beq_eq_true hD
    rw [hs] at h
    exact h

theorem ch36408_echi_all (he : e < 12) : ch36408_echi e = true := by
  have hH := ch36408_echiH_all e he
  rw [ch36408_echiH] at hH
  have hG := ch36408_ehH_all e he
  simp only [ch36408_ehH, Bool.and_eq_true] at hG
  rw [ch36408_echi, chiB, Bool.and_eq_true]
  refine ⟨hH, allB_true_iff.2 fun c hc => allB_true_iff.2 fun s hs => ?_⟩
  have h := wrE_bit he (Eq.mp Nat.blt_eq (allB_true_iff.1 hG.1.2 s hs)) hc
  change Nat.beq (bit (wrX e) (wrEM e (l16 (wrED e 5) s) c))
    (Nat.xor (bit (wrX e) (l16 (wrED e 5) s)) (bit (wrX e) c)) = true
  rw [h]
  exact Nat.beq_refl _

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
  have Me := tm_model wr_model E hFA (wrE_g_lt he) hg
  have hl := ch36408_elab_all he Me
  have hh := ch36408_eh_all he
  have hc := ch36408_ecm_all he
  have h12 := ch36408_el12_all he
  simp only [ch36408_elab, ch36408_eh, ch36408_ecm, ch36408_el12, Bool.and_eq_true] at hl hh hc h12
  obtain ⟨h, hht, q, hq, hi⟩ := e14_complete (W2 := fun r1 => wrED e (Nat.add 19 r1))
    (SP := fun r2 => wrED e (Nat.add 19 (Nat.add (wrEP e 6) r2))) rfl Me hh.1.2 (ch36408_eord_all he) hl.1 hl.2
    (hcOK16_of_hOK16 hh.1.1) hh.2 hc.1.1 hc.1.2 hc.2 h12.1 h12.2 (ch36408_el3_all he)
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
  have hl := ch36408_elab_all he M
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
