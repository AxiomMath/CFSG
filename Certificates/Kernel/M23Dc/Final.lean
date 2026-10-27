module

public import Certificates.Kernel.M23Dc.Bridge
public import Certificates.Kernel.M23Dc.Lit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.Certificates.Kernel.SporLatDcSortSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card)

theorem mw_len : J.mw.length = 16 := rfl

theorem mw_size : m23LatK.mw.size = 16 := rfl

theorem mw_get (j : ℕ) : m23LatK.mw[j]! = J.mw.getD j [] := by
  change J.mw.toArray[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem mt_get {j : ℕ} (hj : j < 16) :
    m23LatK.mt[j]! = (m23LatK.mw[j]!).map (wordTabA #[m23ta.toArray, m23tb.toArray] 23) := by
  rw [wordTabA_eq_L]
  change (J.mw.toArray.map _)[j]! = (J.mw.toArray[j]!).map _
  rw [getElem!_pos _ j (by simp [mw_len, hj]), getElem!_pos J.mw.toArray j (by simp [mw_len, hj])]
  simp

theorem Om_get {j : ℕ} (hj : j < 16) : m23LatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem T_eq : T 0 = m23ta.toArray ∧ T 1 = m23tb.toArray ∧ sT = m23STabs := by
  simp [T, sT, tabs_eq, m23STabs, m23Qp]

theorem mLet_eq {j : ℕ} (hj : j < 16) : (m23LatK.sTabs ++ m23LatK.mt[j]!).toArray = mLet j := by
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

theorem m23K_membersOK :
    MembersOK (codeSetAct 23) 23 m23ta.toArray m23tb.toArray m23Delta m23LatK := by
  refine ⟨by rw [mw_size]; decide, by rw [mw_get]; rfl, by simp [m23LatK], rfl, fun j hj => ?_⟩
  have hj' : j < 16 := hj
  refine ⟨by rw [mw_get]; exact mw_lt2, mt_get hj', ?_⟩
  rw [mLet_eq hj', delta_eq, Om_get hj']
  exact omCodeC_sound (M.all j hj')

theorem m23_delta_valid : CodeSetValid 23 m23Delta := by
  have h : ∀ l ∈ m23Sets, PtValid 23 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m23Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem hel : ∀ l < (#[m23GenA, m23GenB] : Array G).size,
    (#[m23ta.toArray, m23tb.toArray] : Array (Array ℕ)).getD l #[] =
      (tab 23 ((#[m23GenA, m23GenB] : Array G).getD l 1)).toArray
  | 0, _ => m23_ta.symm
  | 1, _ => m23_tb.symm
  | _ + 2, h => absurd h (by simp)

theorem lab_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    lab 23 (codeSetLab 23) m23Delta (wordElt m23GenA m23GenB w) =
      codeSetT 23 (wordTabL #[T 0, T 1] 23 w) Δc := by
  change codeSetAct 23 (tab 23 (evalElt #[m23GenA, m23GenB] w)).toArray m23Delta = _
  rw [← wordTabA_eq #[m23GenA, m23GenB] _ hel w (by simpa using hw), codeSetAct_eq, delta_eq,
    wordTabA_eq_L, T_eq.1, T_eq.2.1]

theorem fixB : (sT.all fun t => codeSetT 23 t Δc == Δc) = true := by quickRfl

theorem moveB : ((List.range' 1 15).all fun j => (J.mw.getD j []).any fun w =>
    !(codeSetT 23 (wordTabL #[T 0, T 1] 23 w) Δc == Δc)) = true := by quickRfl

theorem topB : (!(codeSetT 23 (T 0) Δc == Δc) || !(codeSetT 23 (T 1) Δc == Δc)) = true := by
  quickRfl

theorem hfix : ∀ s ∈ m23Sg, lab 23 (codeSetLab 23) m23Delta s = m23Delta := by
  intro s hs
  have ht : (tab 23 s).toArray ∈ sT := by
    rw [T_eq.2.2, ← m23_sGens.1]
    exact List.mem_map_of_mem hs
  change codeSetAct 23 (tab 23 s).toArray m23Delta = m23Delta
  rw [codeSetAct_eq, delta_eq]
  exact beq_iff_eq.1 (List.all_eq_true.1 fixB _ ht)

theorem hmove : ∀ j, 0 < j → j < J.mw.length → ∃ w ∈ J.mw.getD j [],
    lab 23 (codeSetLab 23) m23Delta (wordElt m23GenA m23GenB w) ≠ m23Delta := by
  intro j h0 hj
  rw [mw_len] at hj
  obtain ⟨w, hw, hne⟩ := List.any_eq_true.1
    (List.all_eq_true.1 moveB j (List.mem_range'_1.2 ⟨h0, by omega⟩))
  refine ⟨w, hw, ?_⟩
  rw [lab_word (mw_lt2 w hw), delta_eq]
  simpa using hne

theorem htop : lab 23 (codeSetLab 23) m23Delta m23GenA ≠ m23Delta ∨
    lab 23 (codeSetLab 23) m23Delta m23GenB ≠ m23Delta := by
  change codeSetAct 23 (tab 23 m23GenA).toArray m23Delta ≠ m23Delta ∨
    codeSetAct 23 (tab 23 m23GenB).toArray m23Delta ≠ m23Delta
  rw [m23_ta, m23_tb, codeSetAct_eq, delta_eq, ← T_eq.1, ← T_eq.2.1]
  have h := topB
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h

theorem m23K_stab : ∀ g : G, lab 23 (codeSetLab 23) m23Delta g = m23Delta ↔
    g ∈ Subgroup.closure {x | x ∈ m23Sg} :=
  stab_of_complete codeSetLab_lawful m23_delta_valid m23GenA m23GenB m23Sg J.mw dc_complete hfix
    (eq_of_beq (by quickRfl : (J.mw.getD 0 [] == []) = true)) hmove htop

theorem m23K_comp : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m23Sg} ≤ Z →
    ∃ j ≤ m23LatK.mw.size, Z = memberOrTop m23LatK.mw.size
      (fun j => Subgroup.closure {x | x ∈ m23Sg ++ (m23LatK.mw[j]!).map
        (wordElt m23GenA m23GenB)}) j := by
  intro Z hZ
  obtain ⟨j, hj, e⟩ := dc_complete Z hZ
  refine ⟨j, by rw [mw_size]; rw [mw_len] at hj; exact hj, ?_⟩
  rw [e, mw_size, ← mw_len]
  simp only [mw_get]

@[expose] noncomputable def m23CtxK : LatCtx G 23 (List ℕ) :=
  LatCtx.ofFacts (codeSetLab 23) (CodeSetValid 23) codeSetLab_lawful m23Delta m23_delta_valid
    m23GenA m23GenB m23ta.toArray m23tb.toArray m23_ta m23_tb m23_gen m23LatK m23Sg 7
    m23_sGens.1 m23_sGens.2 79695 (by rw [m23_card]; norm_num) m23K_membersOK m23K_stab
    m23K_comp

theorem m23K_D_mw : m23CtxK.D.mw = m23LatK.mw := rfl

theorem m23K_D_Om : m23CtxK.D.Om = m23LatK.Om := rfl

theorem m23K_J : m23CtxK.J = 16 := by
  unfold LatCtx.J
  rw [m23K_D_mw, mw_size]

theorem omSizesB : ((List.range 16).map (fun j => (Om j).lbl.size) ==
    [1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9]) = true := by quickRfl

theorem m23K_Om_size : m23CtxK.D.Om.map (fun o => o.lbl.size) =
    #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] := by
  have h := eq_of_beq omSizesB
  rw [m23K_D_Om]
  apply Array.toList_inj.1
  change (Array.map _ #[Om 0, Om 1, Om 2, Om 3, Om 4, Om 5, Om 6, Om 7, Om 8, Om 9, Om 10, Om 11,
    Om 12, Om 13, Om 14, Om 15]).toList = _
  simpa [List.range_succ] using h

theorem m23K_complete : ∀ Z : Subgroup G, m23CtxK.S ≤ Z →
    ∃ j ≤ 16, Z = memberOrTop 16 m23CtxK.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := m23CtxK.complete Z hZ
  rw [m23K_J] at hj ⊢
  exact ⟨j, hj, rfl⟩

end CFSG.KD.M23Dc

end
