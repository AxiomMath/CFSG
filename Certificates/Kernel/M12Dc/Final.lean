module

public import Certificates.Kernel.M12Dc.Bridge
public import Certificates.Kernel.M12Dc.Lit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M12Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Mathieu (m12a m12b card_M12 m12_hyp)

theorem mw_len : J.mw.length = 3 := rfl

theorem mw_size : m12LatK.mw.size = 3 := rfl

theorem mw_get (j : ℕ) : m12LatK.mw[j]! = J.mw.getD j [] := by
  change J.mw.toArray[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem mt_get {j : ℕ} (hj : j < 3) :
    m12LatK.mt[j]! = (m12LatK.mw[j]!).map (wordTabA #[m12ta.toArray, m12tb.toArray] 12) := by
  rw [wordTabA_eq_L]
  change (J.mw.toArray.map _)[j]! = (J.mw.toArray[j]!).map _
  rw [getElem!_pos _ j (by simp [mw_len, hj]), getElem!_pos J.mw.toArray j (by simp [mw_len, hj])]
  simp

theorem Om_get {j : ℕ} (hj : j < 3) : m12LatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem T_eq : T 0 = m12ta.toArray ∧ T 1 = m12tb.toArray ∧ sT = m12STabs := by
  simp [T, sT, tabs_eq, m12STabs, m12Qp]

theorem mLet_eq {j : ℕ} (hj : j < 3) : (m12LatK.sTabs ++ m12LatK.mt[j]!).toArray = mLet j := by
  rw [mt_get hj, mw_get, wordTabA_eq_L]
  unfold mLet
  rw [T_eq.1, T_eq.2.1, T_eq.2.2]
  rfl

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

theorem m12K_membersOK :
    MembersOK (codeSetAct 12) 12 m12ta.toArray m12tb.toArray m12Delta m12LatK := by
  refine ⟨by rw [mw_size]; decide, by rw [mw_get]; rfl, by simp [m12LatK], rfl, fun j hj => ?_⟩
  have hj' : j < 3 := hj
  refine ⟨by rw [mw_get]; exact mw_lt2, mt_get hj', ?_⟩
  rw [mLet_eq hj', delta_eq, Om_get hj']
  exact omCode_sound (List.all_eq_true.1 mems j (List.mem_range.2 hj'))

theorem m12_delta_valid : CodeSetValid 12 m12Delta := by
  have h : ∀ l ∈ m12Sets, PtValid 12 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m12Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem hel : ∀ l < (#[m12a, m12b] : Array G).size,
    (#[m12ta.toArray, m12tb.toArray] : Array (Array ℕ)).getD l #[] =
      (tab 12 ((#[m12a, m12b] : Array G).getD l 1)).toArray
  | 0, _ => m12_ta.symm
  | 1, _ => m12_tb.symm
  | _ + 2, h => absurd h (by simp)

theorem lab_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    lab 12 (codeSetLab 12) m12Delta (wordElt m12a m12b w) =
      codeSetT 12 (wordTabL #[T 0, T 1] 12 w) Δc := by
  change codeSetAct 12 (tab 12 (evalElt #[m12a, m12b] w)).toArray m12Delta = _
  rw [← wordTabA_eq #[m12a, m12b] _ hel w (by simpa using hw), codeSetAct_eq, delta_eq,
    wordTabA_eq_L, T_eq.1, T_eq.2.1]

theorem fixB : (sT.all fun t => codeSetT 12 t Δc == Δc) = true := by quickRfl

theorem moveB : ((List.range' 1 2).all fun j => (J.mw.getD j []).any fun w =>
    !(codeSetT 12 (wordTabL #[T 0, T 1] 12 w) Δc == Δc)) = true := by quickRfl

theorem topB : (!(codeSetT 12 (T 0) Δc == Δc) || !(codeSetT 12 (T 1) Δc == Δc)) = true := by
  quickRfl

theorem hfix : ∀ s ∈ m12Sg, lab 12 (codeSetLab 12) m12Delta s = m12Delta := by
  intro s hs
  have ht : (tab 12 s).toArray ∈ sT := by
    rw [T_eq.2.2, ← m12_sGens.1]
    exact List.mem_map_of_mem hs
  change codeSetAct 12 (tab 12 s).toArray m12Delta = m12Delta
  rw [codeSetAct_eq, delta_eq]
  exact beq_iff_eq.1 (List.all_eq_true.1 fixB _ ht)

theorem hmove : ∀ j, 0 < j → j < J.mw.length → ∃ w ∈ J.mw.getD j [],
    lab 12 (codeSetLab 12) m12Delta (wordElt m12a m12b w) ≠ m12Delta := by
  intro j h0 hj
  rw [mw_len] at hj
  obtain ⟨w, hw, hne⟩ := List.any_eq_true.1
    (List.all_eq_true.1 moveB j (List.mem_range'_1.2 ⟨h0, by omega⟩))
  refine ⟨w, hw, ?_⟩
  rw [lab_word (mw_lt2 w hw), delta_eq]
  simpa using hne

theorem htop : lab 12 (codeSetLab 12) m12Delta m12a ≠ m12Delta ∨
    lab 12 (codeSetLab 12) m12Delta m12b ≠ m12Delta := by
  change codeSetAct 12 (tab 12 m12a).toArray m12Delta ≠ m12Delta ∨
    codeSetAct 12 (tab 12 m12b).toArray m12Delta ≠ m12Delta
  rw [m12_ta, m12_tb, codeSetAct_eq, delta_eq, ← T_eq.1, ← T_eq.2.1]
  have h := topB
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h

theorem m12K_stab : ∀ g : G, lab 12 (codeSetLab 12) m12Delta g = m12Delta ↔
    g ∈ Subgroup.closure {x | x ∈ m12Sg} :=
  stab_of_complete codeSetLab_lawful m12_delta_valid m12a m12b m12Sg J.mw dc_complete hfix
    (eq_of_beq (by quickRfl : (J.mw.getD 0 [] == []) = true)) hmove htop

theorem m12K_comp : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m12Sg} ≤ Z →
    ∃ j ≤ m12LatK.mw.size, Z = memberOrTop m12LatK.mw.size
      (fun j => Subgroup.closure {x | x ∈ m12Sg ++ (m12LatK.mw[j]!).map (wordElt m12a m12b)}) j := by
  intro Z hZ
  obtain ⟨j, hj, e⟩ := dc_complete Z hZ
  refine ⟨j, by rw [mw_size]; rw [mw_len] at hj; exact hj, ?_⟩
  rw [e, mw_size, ← mw_len]
  simp only [mw_get]

@[expose] noncomputable def m12CtxK : LatCtx G 12 (List ℕ) :=
  LatCtx.ofFacts (codeSetLab 12) (CodeSetValid 12) codeSetLab_lawful m12Delta m12_delta_valid
    m12a m12b m12ta.toArray m12tb.toArray m12_ta m12_tb m12_hyp.gen m12LatK m12Sg 6
    m12_sGens.1 m12_sGens.2 1485 (by rw [card_M12]; norm_num) m12K_membersOK m12K_stab m12K_comp

theorem m12K_D_mw : m12CtxK.D.mw = m12LatK.mw := rfl

theorem m12K_D_Om : m12CtxK.D.Om = m12LatK.Om := rfl

theorem m12K_J : m12CtxK.J = 3 := by
  unfold LatCtx.J
  rw [m12K_D_mw, mw_size]

theorem m12K_Om_size : m12CtxK.D.Om.map (fun o => o.lbl.size) = #[1, 3, 3] := by
  have h : [(Om 0).lbl.size, (Om 1).lbl.size, (Om 2).lbl.size] = [1, 3, 3] :=
    eq_of_beq (by quickRfl : ([(Om 0).lbl.size, (Om 1).lbl.size, (Om 2).lbl.size] == [1, 3, 3]) =
      true)
  rw [m12K_D_Om]
  apply Array.toList_inj.1
  change (Array.map _ #[Om 0, Om 1, Om 2]).toList = _
  simpa using h

theorem m12K_complete : ∀ Z : Subgroup G, m12CtxK.S ≤ Z →
    ∃ j ≤ 3, Z = memberOrTop 3 m12CtxK.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := m12CtxK.complete Z hZ
  rw [m12K_J] at hj ⊢
  exact ⟨j, hj, rfl⟩

end CFSG.KD.M12Dc

end
