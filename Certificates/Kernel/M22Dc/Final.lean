module

public import Certificates.Kernel.M22Dc.Bridge
public import Certificates.Kernel.M22Dc.Lit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M22Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Mathieu (m22a m22b card_M22 m22_hyp)

theorem mw_len : J.mw.length = 5 := rfl

theorem mw_size : m22LatK.mw.size = 5 := rfl

theorem mw_get (j : ℕ) : m22LatK.mw[j]! = J.mw.getD j [] := by
  change J.mw.toArray[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem mt_get {j : ℕ} (hj : j < 5) :
    m22LatK.mt[j]! = (m22LatK.mw[j]!).map (wordTabA #[m22ta.toArray, m22tb.toArray] 22) := by
  rw [wordTabA_eq_L]
  change (J.mw.toArray.map _)[j]! = (J.mw.toArray[j]!).map _
  rw [getElem!_pos _ j (by simp [mw_len, hj]), getElem!_pos J.mw.toArray j (by simp [mw_len, hj])]
  simp

theorem Om_get {j : ℕ} (hj : j < 5) : m22LatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem T_eq : T 0 = m22ta.toArray ∧ T 1 = m22tb.toArray ∧ sT = m22STabs := by
  simp [T, sT, tabs_eq, m22STabs, m22Qp]

theorem mLet_eq {j : ℕ} (hj : j < 5) : (m22LatK.sTabs ++ m22LatK.mt[j]!).toArray = mLet j := by
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

theorem m22K_membersOK :
    MembersOK (codeSetAct 22) 22 m22ta.toArray m22tb.toArray m22Delta m22LatK := by
  refine ⟨by rw [mw_size]; decide, by rw [mw_get]; rfl, by simp [m22LatK], rfl, fun j hj => ?_⟩
  have hj' : j < 5 := hj
  refine ⟨by rw [mw_get]; exact mw_lt2, mt_get hj', ?_⟩
  rw [mLet_eq hj', delta_eq, Om_get hj']
  exact omCode_sound (List.all_eq_true.1 mems j (List.mem_range.2 hj'))

theorem m22_delta_valid : CodeSetValid 22 m22Delta := by
  have h : ∀ l ∈ m22Sets, PtValid 22 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m22Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem hel : ∀ l < (#[m22a, m22b] : Array G).size,
    (#[m22ta.toArray, m22tb.toArray] : Array (Array ℕ)).getD l #[] =
      (tab 22 ((#[m22a, m22b] : Array G).getD l 1)).toArray
  | 0, _ => m22_ta.symm
  | 1, _ => m22_tb.symm
  | _ + 2, h => absurd h (by simp)

theorem lab_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    lab 22 (codeSetLab 22) m22Delta (wordElt m22a m22b w) =
      codeSetT 22 (wordTabL #[T 0, T 1] 22 w) Δc := by
  change codeSetAct 22 (tab 22 (evalElt #[m22a, m22b] w)).toArray m22Delta = _
  rw [← wordTabA_eq #[m22a, m22b] _ hel w (by simpa using hw), codeSetAct_eq, delta_eq,
    wordTabA_eq_L, T_eq.1, T_eq.2.1]

theorem fixB : (sT.all fun t => codeSetT 22 t Δc == Δc) = true := by quickRfl

theorem moveB : ((List.range' 1 4).all fun j => (J.mw.getD j []).any fun w =>
    !(codeSetT 22 (wordTabL #[T 0, T 1] 22 w) Δc == Δc)) = true := by quickRfl

theorem topB : (!(codeSetT 22 (T 0) Δc == Δc) || !(codeSetT 22 (T 1) Δc == Δc)) = true := by
  quickRfl

theorem hfix : ∀ s ∈ m22Sg, lab 22 (codeSetLab 22) m22Delta s = m22Delta := by
  intro s hs
  have ht : (tab 22 s).toArray ∈ sT := by
    rw [T_eq.2.2, ← m22_sGens.1]
    exact List.mem_map_of_mem hs
  change codeSetAct 22 (tab 22 s).toArray m22Delta = m22Delta
  rw [codeSetAct_eq, delta_eq]
  exact beq_iff_eq.1 (List.all_eq_true.1 fixB _ ht)

theorem hmove : ∀ j, 0 < j → j < J.mw.length → ∃ w ∈ J.mw.getD j [],
    lab 22 (codeSetLab 22) m22Delta (wordElt m22a m22b w) ≠ m22Delta := by
  intro j h0 hj
  rw [mw_len] at hj
  obtain ⟨w, hw, hne⟩ := List.any_eq_true.1
    (List.all_eq_true.1 moveB j (List.mem_range'_1.2 ⟨h0, by omega⟩))
  refine ⟨w, hw, ?_⟩
  rw [lab_word (mw_lt2 w hw), delta_eq]
  simpa using hne

theorem htop : lab 22 (codeSetLab 22) m22Delta m22a ≠ m22Delta ∨
    lab 22 (codeSetLab 22) m22Delta m22b ≠ m22Delta := by
  change codeSetAct 22 (tab 22 m22a).toArray m22Delta ≠ m22Delta ∨
    codeSetAct 22 (tab 22 m22b).toArray m22Delta ≠ m22Delta
  rw [m22_ta, m22_tb, codeSetAct_eq, delta_eq, ← T_eq.1, ← T_eq.2.1]
  have h := topB
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h

theorem m22K_stab : ∀ g : G, lab 22 (codeSetLab 22) m22Delta g = m22Delta ↔
    g ∈ Subgroup.closure {x | x ∈ m22Sg} :=
  stab_of_complete codeSetLab_lawful m22_delta_valid m22a m22b m22Sg J.mw dc_complete hfix
    (eq_of_beq (by quickRfl : (J.mw.getD 0 [] == []) = true)) hmove htop

theorem m22K_comp : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m22Sg} ≤ Z →
    ∃ j ≤ m22LatK.mw.size, Z = memberOrTop m22LatK.mw.size
      (fun j => Subgroup.closure {x | x ∈ m22Sg ++ (m22LatK.mw[j]!).map (wordElt m22a m22b)}) j := by
  intro Z hZ
  obtain ⟨j, hj, e⟩ := dc_complete Z hZ
  refine ⟨j, by rw [mw_size]; rw [mw_len] at hj; exact hj, ?_⟩
  rw [e, mw_size, ← mw_len]
  simp only [mw_get]

@[expose] noncomputable def m22CtxK : LatCtx G 22 (List ℕ) :=
  LatCtx.ofFacts (codeSetLab 22) (CodeSetValid 22) codeSetLab_lawful m22Delta m22_delta_valid
    m22a m22b m22ta.toArray m22tb.toArray m22_ta m22_tb m22_hyp.gen m22LatK m22Sg 7
    m22_sGens.1 m22_sGens.2 3465 (by rw [card_M22]; norm_num) m22K_membersOK m22K_stab m22K_comp

theorem m22K_D_mw : m22CtxK.D.mw = m22LatK.mw := rfl

theorem m22K_D_Om : m22CtxK.D.Om = m22LatK.Om := rfl

theorem m22K_J : m22CtxK.J = 5 := by
  unfold LatCtx.J
  rw [m22K_D_mw, mw_size]

theorem m22K_Om_size : m22CtxK.D.Om.map (fun o => o.lbl.size) = #[1, 45, 3, 15, 3] := by
  have h : [(Om 0).lbl.size, (Om 1).lbl.size, (Om 2).lbl.size, (Om 3).lbl.size,
      (Om 4).lbl.size] = [1, 45, 3, 15, 3] :=
    eq_of_beq (by quickRfl : ([(Om 0).lbl.size, (Om 1).lbl.size, (Om 2).lbl.size,
      (Om 3).lbl.size, (Om 4).lbl.size] == [1, 45, 3, 15, 3]) = true)
  rw [m22K_D_Om]
  apply Array.toList_inj.1
  change (Array.map _ #[Om 0, Om 1, Om 2, Om 3, Om 4]).toList = _
  simpa using h

theorem m22K_complete : ∀ Z : Subgroup G, m22CtxK.S ≤ Z →
    ∃ j ≤ 5, Z = memberOrTop 5 m22CtxK.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := m22CtxK.complete Z hZ
  rw [m22K_J] at hj ⊢
  exact ⟨j, hj, rfl⟩

end CFSG.KD.M22Dc

end
