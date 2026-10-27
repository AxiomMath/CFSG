
module

public import Certificates.Kernel.J2Dc.Bridge
public import Certificates.Kernel.J2Dc.Lit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J2Lat

theorem mw_len : J.mw.length = 5 := rfl

theorem mw_size : j2LatK.mw.size = 5 := rfl

theorem mw_get (j : ℕ) : j2LatK.mw[j]! = J.mw.getD j [] := by
  change J.mw.toArray[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem mt_get {j : ℕ} (hj : j < 5) :
    j2LatK.mt[j]! = (j2LatK.mw[j]!).map (wordTabA #[j2ta.toArray, j2tb.toArray] 315) := by
  rw [wordTabA_eq_L]
  change (J.mw.toArray.map _)[j]! = (J.mw.toArray[j]!).map _
  rw [getElem!_pos _ j (by simp [mw_len, hj]), getElem!_pos J.mw.toArray j (by simp [mw_len, hj])]
  simp

theorem Om_get {j : ℕ} (hj : j < 5) : j2LatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem mwB : (J.mw.all fun ws => ws.all fun w => w.all (· < 2)) = true := by quickRfl

theorem mw_lt2 {j : ℕ} : ∀ w ∈ J.mw.getD j [], ∀ l ∈ w, l < 2 := by
  intro w hw l hl
  rcases Nat.lt_or_ge j J.mw.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj] at hw
    have h1 := List.all_eq_true.1 mwB _ (List.getElem_mem hj)
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 w hw) l hl
    simpa using h2
  · rw [List.getD_eq_default _ _ hj] at hw
    simp at hw

theorem T_eq : T 0 = j2ta.toArray ∧ T 1 = j2tb.toArray ∧ sT = j2STabs := by
  refine ⟨(tab_letter (l := 0) (by decide)).symm.trans j2_ta',
    (tab_letter (l := 1) (by decide)).symm.trans j2_tb', ?_⟩
  have e : ∀ i, (h : i < 3) → T (i + 2) = j2SLP[[155, 166, 179].getD i 0]! := by
    intro i h
    rw [← tab_letter (by omega)]
    interval_cases i <;> exact tab_node (by decide)
  simp only [sT, j2STabs, j2Qp, List.map_cons, List.map_nil]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
  rfl

theorem mLet_eq {j : ℕ} (hj : j < 5) : (j2LatK.sTabs ++ j2LatK.mt[j]!).toArray = mLet j := by
  rw [mt_get hj, mw_get, wordTabA_eq_L]
  unfold mLet
  rw [T_eq.1, T_eq.2.1, T_eq.2.2]
  rfl

theorem j2K_membersOK :
    MembersOK (codeSetAct 315) 315 j2ta.toArray j2tb.toArray j2Delta j2LatK := by
  refine ⟨by rw [mw_size]; decide, by rw [mw_get]; rfl, by simp [j2LatK], rfl, fun j hj => ?_⟩
  have hj' : j < 5 := hj
  refine ⟨by rw [mw_get]; exact mw_lt2, mt_get hj', ?_⟩
  rw [mLet_eq hj', delta_eq, Om_get hj']
  exact omCode_sound (List.all_eq_true.1 mems j (List.mem_range.2 hj'))

theorem hel : ∀ l < (#[ga, gb] : Array G).size,
    (#[j2ta.toArray, j2tb.toArray] : Array (Array ℕ)).getD l #[] =
      (tab 315 ((#[ga, gb] : Array G).getD l 1)).toArray
  | 0, _ => j2_ta'.symm
  | 1, _ => j2_tb'.symm
  | _ + 2, h => absurd h (by simp)

theorem lab_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    lab 315 (codeSetLab 315) j2Delta (wordElt ga gb w) =
      codeSetT 315 (wordTabL #[T 0, T 1] 315 w) Δc := by
  change codeSetAct 315 (tab 315 (evalElt #[ga, gb] w)).toArray j2Delta = _
  rw [← wordTabA_eq #[ga, gb] _ hel w (by simpa using hw), codeSetAct_eq, delta_eq,
    wordTabA_eq_L, T_eq.1, T_eq.2.1]

theorem fixB : (sT.all fun t => codeSetT 315 t Δc == Δc) = true := by quickRfl

theorem moveB : ((List.range' 1 4).all fun j => (J.mw.getD j []).any fun w =>
    !(codeSetT 315 (wordTabL #[T 0, T 1] 315 w) Δc == Δc)) = true := by quickRfl

theorem topB : (!(codeSetT 315 (T 0) Δc == Δc) || !(codeSetT 315 (T 1) Δc == Δc)) = true := by
  quickRfl

theorem hfix : ∀ s ∈ j2SgK, lab 315 (codeSetLab 315) j2Delta s = j2Delta := by
  intro s hs
  have ht : (tab 315 s).toArray ∈ sT := by
    rw [T_eq.2.2, ← j2K_sGens.1]
    exact List.mem_map_of_mem hs
  change codeSetAct 315 (tab 315 s).toArray j2Delta = j2Delta
  rw [codeSetAct_eq, delta_eq]
  exact beq_iff_eq.1 (List.all_eq_true.1 fixB _ ht)

theorem hmove : ∀ j, 0 < j → j < J.mw.length → ∃ w ∈ J.mw.getD j [],
    lab 315 (codeSetLab 315) j2Delta (wordElt ga gb w) ≠ j2Delta := by
  intro j h0 hj
  rw [mw_len] at hj
  obtain ⟨w, hw, hne⟩ := List.any_eq_true.1
    (List.all_eq_true.1 moveB j (List.mem_range'_1.2 ⟨h0, by omega⟩))
  refine ⟨w, hw, ?_⟩
  rw [lab_word (mw_lt2 w hw), delta_eq]
  simpa using hne

theorem htop : lab 315 (codeSetLab 315) j2Delta ga ≠ j2Delta ∨
    lab 315 (codeSetLab 315) j2Delta gb ≠ j2Delta := by
  change codeSetAct 315 (tab 315 ga).toArray j2Delta ≠ j2Delta ∨
    codeSetAct 315 (tab 315 gb).toArray j2Delta ≠ j2Delta
  rw [j2_ta', j2_tb', codeSetAct_eq, delta_eq, ← T_eq.1, ← T_eq.2.1]
  have h := topB
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h

theorem j2K_stab : ∀ g : G, lab 315 (codeSetLab 315) j2Delta g = j2Delta ↔
    g ∈ Subgroup.closure {x | x ∈ j2SgK} :=
  stab_of_complete codeSetLab_lawful j2_delta_valid ga gb j2SgK J.mw dc_complete hfix
    (eq_of_beq (by quickRfl : (J.mw.getD 0 [] == []) = true)) hmove htop

theorem j2K_comp : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ j2SgK} ≤ Z →
    ∃ j ≤ j2LatK.mw.size, Z = memberOrTop j2LatK.mw.size
      (fun j => Subgroup.closure {x | x ∈ j2SgK ++ (j2LatK.mw[j]!).map (wordElt ga gb)}) j := by
  intro Z hZ
  obtain ⟨j, hj, e⟩ := dc_complete Z hZ
  refine ⟨j, by rw [mw_size]; rw [mw_len] at hj; exact hj, ?_⟩
  have hs : j2LatK.mw.size = J.mw.length := rfl
  rw [e, hs]
  simp only [mw_get]

@[expose] noncomputable def j2CtxK : LatCtx G 315 (List ℕ) :=
  LatCtx.ofFacts (codeSetLab 315) (CodeSetValid 315) codeSetLab_lawful j2Delta j2_delta_valid
    ga gb j2ta.toArray j2tb.toArray j2_ta' j2_tb' CFSG.Sporadic.J2.closure_ab j2LatK j2SgK 7
    j2K_sGens.1 j2K_sGens.2 4725 (by rw [CFSG.Sporadic.J2.card_J]; norm_num) j2K_membersOK j2K_stab
    j2K_comp

theorem j2K_D_Om : j2CtxK.D.Om = j2LatK.Om := rfl

theorem j2K_Om_size : j2CtxK.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := by
  have h : [(Om 0).lbl.size, (Om 1).lbl.size, (Om 2).lbl.size, (Om 3).lbl.size,
      (Om 4).lbl.size] = [1, 3, 9, 15, 3] :=
    eq_of_beq (by quickRfl : ([(Om 0).lbl.size, (Om 1).lbl.size, (Om 2).lbl.size,
      (Om 3).lbl.size, (Om 4).lbl.size] == [1, 3, 9, 15, 3]) = true)
  rw [j2K_D_Om]
  apply Array.toList_inj.1
  change (Array.map _ #[Om 0, Om 1, Om 2, Om 3, Om 4]).toList = _
  simpa using h

end CFSG.KD.J2Dc

end
