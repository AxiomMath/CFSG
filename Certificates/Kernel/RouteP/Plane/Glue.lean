module

public import Certificates.Kernel.RouteP.Plane.Nets
public import Certificates.Kernel.RouteP.Plane.Act0
public import Certificates.Kernel.RouteP.Plane.Act1
public import Certificates.Kernel.RouteP.Plane.Act2
public import Certificates.Kernel.RouteP.Plane.Act3
public import Certificates.Kernel.RouteP.Plane.Act4
public import Certificates.Kernel.RouteP.Plane.Act5
public import Certificates.Kernel.RouteP.Plane.Act6
public import Certificates.Kernel.RouteP.Text.PlaneFacts
public import Certificates.Kernel.RouteP.Text.Texts
public import Certificates.Kernel.RouteP.Obj.Run
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Tables
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

#kc_forall_tree pnk_all (fun e => CFSG.KD.RouteP.pnk e = true) 3 CFSG.KD.RouteP.PlaneCk.n
#kc_forall_tree pwck_all (fun g => CFSG.KD.RouteP.pwck g = true) 60 CFSG.KD.RouteP.PlaneCk.w
#kc_forall_tree pfck_all (fun g => CFSG.KD.RouteP.pfck g = true) 48 CFSG.KD.RouteP.PlaneCk.f
#kc_forall_tree pack_all (fun g => CFSG.KD.RouteP.pack g = true) 12474 CFSG.KD.RouteP.PlaneCk.a

theorem pnkA : ∀ e < 3, pnk e = true := pnk_all

theorem pwckA : ∀ g < 60, pwck g = true := pwck_all

theorem pfckA : ∀ g < 48, pfck g = true := pfck_all

theorem packA : ∀ g < 12474, pack g = true := pack_all

theorem NWQ_lt {j : Nat} (hj : j < 58) : NWQ j = NWO j := by
  funext l
  unfold NWQ
  rw [(Nat.blt_eq.mpr hj : Nat.blt j 58 = true)]

theorem KAQ_lt {j : Nat} (hj : j < 58) : KAQ j = KAO j := by
  unfold KAQ KAO
  rw [NWQ_lt hj]

theorem KBQ_lt {j : Nat} (hj : j < 58) : KBQ j = KBO j := by
  unfold KBQ KBO
  rw [NWQ_lt hj]

theorem kapOK_congr {KA KB KA' KB' : Nat → Nat} {j : Nat} (ha : KA j = KA' j) (hb : KB j = KB' j) :
    kapOK KA KB j = kapOK KA' KB' j := by
  unfold kapOK
  rw [ha, hb]

theorem eL_Q {z : ℤ} (hz : z.natAbs - 1 < 58) (N : Nat) : eL NWQ KAQ KBQ z N = eL NWO KAO KBO z N := by
  cases z with
  | ofNat m =>
    have hm : m - 1 < 58 := hz
    simp only [eL, fibF, lK, NWQ_lt hm, KAQ_lt hm, KBQ_lt hm]
  | negSucc m =>
    have hm : m < 58 := by simpa using hz
    simp only [eL, fibF, lK, NWQ_lt hm, KAQ_lt hm, KBQ_lt hm]

theorem lokQ' {j : Nat} (hj : j < 61) :
    CFSG.KC.Fi24Net.netOK (NWQ j) = true ∧ kapOK KAQ KBQ j = true := by
  by_cases h : j < 58
  · obtain ⟨h1, h2⟩ := lokO (z := Int.ofNat (j + 1)) (by change j + 1 - 1 < 58; omega)
    refine ⟨?_, ?_⟩
    · rw [NWQ_lt h]
      exact h1
    · rw [kapOK_congr (KAQ_lt h) (KBQ_lt h)]
      exact h2
  · have hp := pnkA (j - 58) (by omega)
    unfold pnk at hp
    have e : Nat.add 58 (j - 58) = j := by
      change 58 + (j - 58) = _
      omega
    rw [e] at hp
    exact CFSG.KC.Benes.andB_true hp

theorem lokQ {z : ℤ} (hz : z.natAbs - 1 < 61) : LOK NWQ KAQ KBQ z := lokQ' hz

noncomputable abbrev πP (k : Nat) : Perm Pt := gO (pReg k)

theorem pReg_lt {k : Nat} (hk : k < 16) : pReg k < 58 := by
  unfold pReg
  split_ifs <;> omega

theorem planeLetterRegs_eq : ∀ k < 16, planeLetterRegs[k]! = pReg k := by decide

theorem planeLetters_size (tabs : Array Table) : (planeLetters tabs).size = 16 := by
  simp [planeLetters, planeLetterRegs]

theorem planeLetters_get (tabs : Array Table) {k : Nat} (hk : k < 16) :
    (planeLetters tabs)[k]! = tabs[pReg k]! := by
  rw [← planeLetterRegs_eq k hk]
  unfold planeLetters
  rw [getElem!_pos _ k (by simp [planeLetterRegs]; omega), List.getElem_toArray, List.getElem_map,
    getElem!_pos planeLetterRegs k (by simp [planeLetterRegs]; omega)]

theorem planeLetters_rep {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) :
    ∀ k < (planeLetters tabs).size, Rep 920808 (planeLetters tabs)[k]! (πP k) := by
  intro k hk
  rw [planeLetters_size] at hk
  rw [planeLetters_get tabs hk]
  exact hR _ (pReg_lt hk)

theorem letter_act {l : ℤ} (hl : 1 ≤ l.natAbs ∧ l.natAbs ≤ 16) (y : Pt) :
    (letterPerm πP 16 l y).val = eL NWQ KAQ KBQ (pl l) y.val := by
  unfold letterPerm pl
  by_cases hp : 0 < l
  · have hk : (l - 1).toNat < 16 := by omega
    rw [if_pos ⟨hp, hk⟩, if_pos hp]
    have e : l.toNat - 1 = (l - 1).toNat := by omega
    rw [e]
    have hr := pReg_lt hk
    have e2 : -((pReg (l - 1).toNat : ℤ) + 1) = Int.negSucc (pReg (l - 1).toNat) := by
      rw [Int.negSucc_eq]
    rw [e2, eL_Q (z := Int.negSucc (pReg (l - 1).toNat)) (by change pReg (l - 1).toNat + 1 - 1 < 58; omega)]
    exact gT_apply (lokO (by change pReg (l - 1).toNat + 1 - 1 < 58; omega)) y
  · have hk : (-l - 1).toNat < 16 := by omega
    rw [if_neg (fun h => hp h.1), if_pos ⟨by omega, hk⟩, if_neg hp]
    have e : (-l).toNat - 1 = (-l - 1).toNat := by omega
    rw [e]
    have hr := pReg_lt hk
    have e2 : ((pReg (-l - 1).toNat : ℤ) + 1) = Int.ofNat (pReg (-l - 1).toNat + 1) := by
      simp
    rw [e2, eL_Q (z := Int.ofNat (pReg (-l - 1).toNat + 1))
      (by change pReg (-l - 1).toNat + 1 - 1 < 58; omega)]
    exact gT_inv_apply (lokO (by change pReg (-l - 1).toNat + 1 - 1 < 58; omega)) y

theorem dWords_eq : planeDWordsK = [dW0, dW1] := by decide +kernel

theorem uWord_eq : planeUWordK = uW := by decide +kernel

theorem vWord_eq : planeVWordK = vW := by decide +kernel

theorem wT_letters : ∀ e < 3, ∀ l ∈ wT e, 1 ≤ l.natAbs ∧ l.natAbs ≤ 16 := by decide

theorem uv_letters : (∀ l ∈ uW, 1 ≤ l.natAbs ∧ l.natAbs ≤ 16) ∧ ∀ l ∈ vW, 1 ≤ l.natAbs ∧ l.natAbs ≤ 16 := by
  decide

theorem wP_lok : ∀ e < 3, ∀ z ∈ wP e, z.natAbs - 1 < 61 := by decide

theorem uv_lok : (∀ z ∈ uW.map pl, z.natAbs - 1 < 61) ∧ ∀ z ∈ vW.map pl, z.natAbs - 1 < 61 := by decide

theorem zl_lok : ∀ s < 14, (zl s).natAbs - 1 < 61 := by decide

theorem planeGenWord_eq {s : Nat} (hs : s < 14) :
    planeGenWord (planeDWords ()) (planeUWord ()) (planeVWord ()) s =
      if s < 2 then wT s else if s < 13 then [(s : ℤ) + 1] else wT 2 := by
  rw [planeDWords_eq, planeUWord_eq, planeVWord_eq, dWords_eq, uWord_eq, vWord_eq]
  unfold planeGenWord
  rcases (by omega : s = 0 ∨ s = 1 ∨ (2 ≤ s ∧ s < 13) ∨ s = 13) with rfl | rfl | h | rfl
  · rfl
  · rfl
  · rw [if_neg (by omega), if_pos h.2, if_neg (by omega), if_pos h.2]
  · rfl

theorem wordG_act {w : List ℤ} (hw : ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 16) (y : Pt) :
    (wordG (letterPerm πP 16) w y).val = eW NWQ KAQ KBQ (w.map pl) y.val :=
  wordG_apply (letterPerm πP 16) pl w (fun l hl y => letter_act (hw l hl) y) y

theorem ap_planeGenTab {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) {w : List ℤ}
    (hw : ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 16) {x : Nat} (hx : x < 920808) :
    ap (planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree)) w) x =
      eW NWQ KAQ KBQ (w.map pl) x := by
  have hrep := planeLetters_rep hR
  have h := rep_wordT_letters (G := Perm Pt) (n := 920808) hn32 hrep
    (fun k hk => invOK_invT_of_rep hn32 (hrep k hk)) w
  rw [planeLetters_size] at h
  unfold planeGenTab
  rw [h x hx, idx_of_lt _ hx, Perm.smul_def, wordG_act hw]

theorem apG {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) {s : Nat} (hs : s < 14)
    {x : Nat} (hx : x < 920808) :
    ap (planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree))
      (planeGenWord (planeDWords ()) (planeUWord ()) (planeVWord ()) s)) x = eL NWQ KAQ KBQ (zl s) x := by
  rw [planeGenWord_eq hs]
  have hnet : ∀ e < 3, ∀ N < 920808, eW NWQ KAQ KBQ (wP e) N = eL NWQ KAQ KBQ (Int.ofNat (58 + e + 1)) N := by
    intro e he N hN
    have hl := lokQ' (j := 58 + e) (by omega)
    have hw : WOK NWQ KAQ KBQ (wP e) := fun z hz => lokQ (wP_lok e he z hz)
    have hpl : ∀ k < 19, CFSG.KC.RouteP.wordOK NWQ (wP e) (58 + e) k = true := by
      intro k hk
      have h := pwckA (20 * e + k) (by omega)
      unfold pwck at h
      have e1 : Nat.div (20 * e + k) 20 = e := by change (20 * e + k) / 20 = e; omega
      have e2 : Nat.mod (20 * e + k) 20 = k := by change (20 * e + k) % 20 = k; omega
      rw [e1, e2] at h
      beta_reduce at h
      rw [Nat.blt_eq.mpr hk] at h
      exact h
    have hk : wordKOK NWQ KAQ KBQ (wP e) (58 + e) = true := by
      have h := pwckA (20 * e + 19) (by omega)
      unfold pwck at h
      have e1 : Nat.div (20 * e + 19) 20 = e := by change (20 * e + 19) / 20 = e; omega
      have e2 : Nat.mod (20 * e + 19) 20 = 19 := by change (20 * e + 19) % 20 = 19; omega
      rw [e1, e2] at h
      exact h
    exact (word_spec hl.1 hl.2 hw hpl hk N hN).symm
  rcases (by omega : s < 2 ∨ (2 ≤ s ∧ s < 13) ∨ s = 13) with h2 | h2 | rfl
  · rw [if_pos h2, ap_planeGenTab hR (wT_letters s (by omega)) hx]
    have e : zl s = Int.ofNat (58 + s + 1) := by
      unfold zl
      rw [if_pos h2, Int.ofNat_eq_coe]
      omega
    rw [e]
    exact hnet s (by omega) x hx
  · rw [if_neg (by omega), if_pos h2.2, ap_planeGenTab hR (by simp; omega) hx]
    unfold zl
    rw [if_neg (by omega), if_pos h2.2]
    rfl
  · rw [if_neg (by omega), if_neg (by omega), ap_planeGenTab hR (wT_letters 2 (by omega)) hx]
    exact hnet 2 (by omega) x hx

theorem pf_spec {t p : Nat} (ht : t < 16) (hp : p < 3) :
    eW NWQ KAQ KBQ (fW t) (fixPt p) = fixPt p := by
  have h := pfckA (3 * t + p) (by omega)
  unfold pfck at h
  have e1 : Nat.div (3 * t + p) 3 = t := by change (3 * t + p) / 3 = t; omega
  have e2 : Nat.mod (3 * t + p) 3 = p := by change (3 * t + p) % 3 = p; omega
  rw [e1, e2] at h
  have hx : fixPt p < 920808 := by unfold fixPt; split_ifs <;> omega
  have hw : ∀ z ∈ fW t, LOK NWQ KAQ KBQ z := by
    intro z hz
    apply lokQ
    unfold fW at hz
    split_ifs at hz with h1 h2
    · rw [List.mem_singleton] at hz
      rw [hz]
      exact zl_lok t h1
    · exact uv_lok.1 z hz
    · exact uv_lok.2 z hz
  exact ptOK_spec hw hx hx h

theorem fixPt_lt {p : Nat} : fixPt p < 920808 := by
  unfold fixPt
  split_ifs <;> omega

theorem fix3_of {T : Table} (h : ∀ p < 3, ap T (fixPt p) = fixPt p) : fix3 T = true := by
  have h0 : ap T 0 = 0 := h 0 (by decide)
  have h1 : ap T 1479 = 1479 := h 1 (by decide)
  have h2 : ap T 99705 = 99705 := h 2 (by decide)
  unfold fix3
  simp [h0, h1, h2]

theorem memS_zero (N : Nat) : memS 0 N = false := by
  unfold memS
  exact Nat.zero_testBit _

theorem memS_rec {f : Nat → Nat} {N : Nat} (hN : N < 920808) :
    ∀ L : List Nat, (∀ j ∈ L, f j < 920808) → (memS (List.rec (motive := fun _ => Nat) 0
      (fun j _ ih => Nat.lor (single (f j)) ih) L) N = true ↔ ∃ j ∈ L, f j = N)
  | [], _ => by
    change memS 0 N = true ↔ _
    simp [memS_zero]
  | j :: L, hf => by
    change memS (Nat.lor (single (f j)) _) N = true ↔ _
    rw [memS_lor, Bool.or_eq_true, memS_single (hf j List.mem_cons_self) hN,
      memS_rec hN L fun j' hj' => hf j' (List.mem_cons_of_mem _ hj')]
    simp only [decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem memS_pS {i : Nat} (hi : i < 891) {N : Nat} (hN : N < 920808) :
    memS (pS i) N = true ↔ ∃ j < 24, PXE i j = N := by
  unfold pS
  rw [memS_rec hN _ fun j hj => (px_rows i hi).1 j (List.mem_range.1 hj)]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, List.mem_range.1 hj, h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, List.mem_range.2 hj, h⟩

theorem pack_spec {s i : Nat} (hs : s < 14) (hi : i < 891) :
    imgS NWQ KAQ KBQ (zl s) (pS i) = pS (PGE s i) := by
  have h := packA (891 * s + i) (by omega)
  unfold pack at h
  have e1 : Nat.div (891 * s + i) 891 = s := by change (891 * s + i) / 891 = s; omega
  have e2 : Nat.mod (891 * s + i) 891 = i := by change (891 * s + i) % 891 = i; omega
  rw [e1, e2] at h
  exact Nat.eq_of_beq_eq_true h

theorem lettersInvOK_of {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) :
    lettersInvOK (planeLetters tabs) = true := by
  unfold lettersInvOK
  rw [Bool.and_eq_true, beq_iff_eq, allIn_iff']
  refine ⟨planeLetters_size tabs, fun l _ hl => ?_⟩
  exact invOK_invT_of_rep hn32 (planeLetters_rep hR l (by rw [planeLetters_size]; exact hl))

theorem planesOKAt_of {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) :
    planesOKAt tabs (planeXData ()) (planeTabs ()) (planePar ()) (planeLab ()) (planeSep ())
      (planeDWords ()) (planeUWord ()) (planeVWord ()) = true := by
  have hG : ∀ s < 14, ∀ x < 920808,
      ap ((Array.range planeGenCount).map fun s => planeGenTab (planeLetters tabs)
        ((planeLetters tabs).map (invT degree))
          (planeGenWord (planeDWords ()) (planeUWord ()) (planeVWord ()) s))[s]! x =
        eL NWQ KAQ KBQ (zl s) x := by
    intro s hs x hx
    rw [getElem!_pos _ s (by simp [planeGenCount]; omega), Array.getElem_map, Array.getElem_range]
    exact apG hR hs hx
  have hGs : ((Array.range planeGenCount).map fun s => planeGenTab (planeLetters tabs)
        ((planeLetters tabs).map (invT degree))
          (planeGenWord (planeDWords ()) (planeUWord ()) (planeVWord ()) s)).size = 14 := by
    simp [planeGenCount]
  unfold planesOKAt
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨lettersInvOK_of hR, rowsOK_true⟩, baseOK_true⟩, distinctOK_true⟩, sepOK_true⟩,
    dwordsOK_true⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, planeTreeOK_true⟩, beq_iff_eq.2 fixMasks_eq⟩
  · unfold fixTripleOK
    rw [Bool.and_eq_true, beq_iff_eq, allIn_iff']
    refine ⟨hGs, fun s _ hs' => fix3_of fun p hp => ?_⟩
    have hs : s < 14 := hs'
    rw [hG s hs _ fixPt_lt]
    have := pf_spec (t := s) (by omega) hp
    unfold fW at this
    rw [if_pos hs] at this
    exact this
  · refine fix3_of fun p hp => ?_
    rw [planeUWord_eq, uWord_eq, ap_planeGenTab hR uv_letters.1 fixPt_lt]
    exact pf_spec (t := 14) (by omega) hp
  · refine fix3_of fun p hp => ?_
    rw [planeVWord_eq, vWord_eq, ap_planeGenTab hR uv_letters.2 fixPt_lt]
    exact pf_spec (t := 15) (by omega) hp
  · obtain ⟨hTs, hTg⟩ := planeTabs_get
    unfold actOK
    simp only [Bool.and_eq_true, beq_iff_eq, allIn_iff', decide_eq_true_eq, planeGenCount, planeCount]
    refine ⟨hTs, fun s _ hs => ⟨(hTg s hs).1, fun i _ hi => ⟨?_, fun a _ ha => ?_⟩⟩⟩
    · rw [(hTg s hs).2 i hi]
      exact pg_lt hs hi
    · rw [(hTg s hs).2 i hi, px_get hi ha]
      have hM := (px_rows i hi).1 a ha
      rw [hG s hs _ hM]
      have hlok := lokQ (zl_lok s hs)
      have hin : memS (pS i) (PXE i a) = true := (memS_pS hi hM).2 ⟨a, ha, rfl⟩
      rw [← memS_imgS hlok (pS i) hM, pack_spec hs hi] at hin
      have hT := pg_lt hs hi
      obtain ⟨b, hb, he⟩ := (memS_pS hT (eL_lt hlok hM)).1 hin
      rw [memRow_iff]
      exact ⟨b, hb, by rw [px_get hT hb, he]⟩

theorem q0PlanesOK_true : q0PlanesOK () = true := planesOKAt_of objRun_rep

end CertificateChecks.KernelRouteP

end
