module

public import Certificates.Kernel.M11Dc.Bridge
public import Certificates.Kernel.M11Dc.Lit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Certificates.Kernel.SporLatDcSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M11Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGSporLat
open CFSG.Sporadic.Mathieu (m11a m11b card_M11 m11_hyp)
open CFSG.QuasithinUnique
open CFSG.Open (pCoreOf)

theorem mw_len : J.mw.length = 4 := rfl

theorem mw_size : m11LatK.mw.size = 4 := rfl

theorem mw_get (j : ℕ) : m11LatK.mw[j]! = J.mw.getD j [] := by
  change J.mw.toArray[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem mt_get {j : ℕ} (hj : j < 4) :
    m11LatK.mt[j]! = (m11LatK.mw[j]!).map (wordTabA #[m11ta.toArray, m11tb.toArray] 11) := by
  rw [wordTabA_eq_L]
  change (J.mw.toArray.map _)[j]! = (J.mw.toArray[j]!).map _
  rw [getElem!_pos _ j (by simp [mw_len, hj]), getElem!_pos J.mw.toArray j (by simp [mw_len, hj])]
  simp

theorem Om_get {j : ℕ} (hj : j < 4) : m11LatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem otD_get {j : ℕ} (hj : j < 4) : m11OtK[j]! = OtD j := by
  interval_cases j <;> rfl

theorem T_eq : T 0 = m11ta.toArray ∧ T 1 = m11tb.toArray ∧ sT = m11STabs := by
  simp [T, sT, tabs_eq, m11STabs, m11Qp]

theorem mLet_eq {j : ℕ} (hj : j < 4) : (m11LatK.sTabs ++ m11LatK.mt[j]!).toArray = mLet j := by
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

theorem m11K_membersOK :
    MembersOK (codeSetAct 11) 11 m11ta.toArray m11tb.toArray m11Delta m11LatK := by
  refine ⟨by rw [mw_size]; decide, by rw [mw_get]; rfl, by simp [m11LatK], rfl, fun j hj => ?_⟩
  have hj' : j < 4 := hj
  refine ⟨by rw [mw_get]; exact mw_lt2, mt_get hj', ?_⟩
  rw [mLet_eq hj', delta_eq, Om_get hj']
  exact omCode_sound (List.all_eq_true.1 mems j (List.mem_range.2 hj'))

theorem m11_delta_valid : CodeSetValid 11 m11Delta := by
  have h : ∀ l ∈ m11Sets, PtValid 11 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m11Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩


theorem hel : ∀ l < (#[m11a, m11b] : Array G).size,
    (#[m11ta.toArray, m11tb.toArray] : Array (Array ℕ)).getD l #[] =
      (tab 11 ((#[m11a, m11b] : Array G).getD l 1)).toArray
  | 0, _ => m11_ta.symm
  | 1, _ => m11_tb.symm
  | _ + 2, h => absurd h (by simp)

theorem lab_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    lab 11 (codeSetLab 11) m11Delta (wordElt m11a m11b w) =
      codeSetT 11 (wordTabL #[T 0, T 1] 11 w) Δc := by
  change codeSetAct 11 (tab 11 (evalElt #[m11a, m11b] w)).toArray m11Delta = _
  rw [← wordTabA_eq #[m11a, m11b] _ hel w (by simpa using hw), codeSetAct_eq, delta_eq,
    wordTabA_eq_L, T_eq.1, T_eq.2.1]

theorem fixB : (sT.all fun t => codeSetT 11 t Δc == Δc) = true := by quickRfl

theorem moveB : ((List.range' 1 3).all fun j => (J.mw.getD j []).any fun w =>
    !(codeSetT 11 (wordTabL #[T 0, T 1] 11 w) Δc == Δc)) = true := by quickRfl

theorem topB : (!(codeSetT 11 (T 0) Δc == Δc) || !(codeSetT 11 (T 1) Δc == Δc)) = true := by
  quickRfl

theorem hfix : ∀ s ∈ m11SgK, lab 11 (codeSetLab 11) m11Delta s = m11Delta := by
  intro s hs
  have ht : (tab 11 s).toArray ∈ sT := by
    rw [T_eq.2.2, ← m11_sGensK.1]
    exact List.mem_map_of_mem hs
  change codeSetAct 11 (tab 11 s).toArray m11Delta = m11Delta
  rw [codeSetAct_eq, delta_eq]
  exact beq_iff_eq.1 (List.all_eq_true.1 fixB _ ht)

theorem hmove : ∀ j, 0 < j → j < J.mw.length → ∃ w ∈ J.mw.getD j [],
    lab 11 (codeSetLab 11) m11Delta (wordElt m11a m11b w) ≠ m11Delta := by
  intro j h0 hj
  rw [mw_len] at hj
  obtain ⟨w, hw, hne⟩ := List.any_eq_true.1
    (List.all_eq_true.1 moveB j (List.mem_range'_1.2 ⟨h0, by omega⟩))
  refine ⟨w, hw, ?_⟩
  rw [lab_word (mw_lt2 w hw), delta_eq]
  simpa using hne

theorem htop : lab 11 (codeSetLab 11) m11Delta m11a ≠ m11Delta ∨
    lab 11 (codeSetLab 11) m11Delta m11b ≠ m11Delta := by
  change codeSetAct 11 (tab 11 m11a).toArray m11Delta ≠ m11Delta ∨
    codeSetAct 11 (tab 11 m11b).toArray m11Delta ≠ m11Delta
  rw [m11_ta, m11_tb, codeSetAct_eq, delta_eq, ← T_eq.1, ← T_eq.2.1]
  have h := topB
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h

theorem m11K_stab : ∀ g : G, lab 11 (codeSetLab 11) m11Delta g = m11Delta ↔
    g ∈ Subgroup.closure {x | x ∈ m11SgK} :=
  stab_of_complete codeSetLab_lawful m11_delta_valid m11a m11b m11SgK J.mw dc_complete hfix
    (eq_of_beq (by quickRfl : (J.mw.getD 0 [] == []) = true)) hmove htop

theorem m11K_comp : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m11SgK} ≤ Z →
    ∃ j ≤ m11LatK.mw.size, Z = memberOrTop m11LatK.mw.size
      (fun j => Subgroup.closure {x | x ∈ m11SgK ++ (m11LatK.mw[j]!).map (wordElt m11a m11b)}) j := by
  intro Z hZ
  obtain ⟨j, hj, e⟩ := dc_complete Z hZ
  refine ⟨j, by rw [mw_size]; rw [mw_len] at hj; exact hj, ?_⟩
  rw [e, mw_size, ← mw_len]
  simp only [mw_get]

@[expose] noncomputable def m11CtxK : LatCtx G 11 (List ℕ) :=
  LatCtx.ofFacts (codeSetLab 11) (CodeSetValid 11) codeSetLab_lawful m11Delta m11_delta_valid
    m11a m11b m11ta.toArray m11tb.toArray m11_ta m11_tb m11_hyp.gen m11LatK m11SgK 4
    m11_sGensK.1 m11_sGensK.2 495 (by rw [card_M11]; norm_num) m11K_membersOK m11K_stab m11K_comp

theorem m11K_D_mw : m11CtxK.D.mw = m11LatK.mw := rfl

theorem m11K_D_Om : m11CtxK.D.Om = m11LatK.Om := rfl

theorem m11K_D_sTabs : m11CtxK.D.sTabs = m11LatK.sTabs := rfl

theorem m11K_k : m11CtxK.k = 4 := rfl

theorem m11K_J : m11CtxK.J = 4 := by
  unfold LatCtx.J
  rw [m11K_D_mw, mw_size]

theorem m11K_o2OK : O2OK (codeSetAct 11) m11CtxK.D m11OtK := by
  unfold O2OK
  rw [m11K_D_mw, m11K_D_Om, m11K_D_sTabs]
  refine ⟨rfl, fun j hj => ?_⟩
  have hj' : j < 4 := hj
  rw [Om_get hj', otD_get hj']
  refine ⟨by interval_cases j <;> rfl, ?_⟩
  have hs : m11LatK.sTabs.toArray = sT.toArray := by rw [T_eq.2.2]; rfl
  rw [hs]
  exact (omOKG_sound (act := tupAct (codeSetAct 11)) (letters := sT.toArray) (fun _ => True)
    trivial (fun l _ X _ => ⟨trivial, by
      unfold tupAct
      rw [codeSetAct_eq, Array.getElem!_eq_getD]
      rfl⟩)
    (List.all_eq_true.1 ots j (List.mem_range.2 hj'))).1

theorem m11K_rows : (List.range 4).map (defaultRow 4 m11CtxK.D m11OtK) = m11Mems := by
  have e : ∀ j ∈ List.range 4, defaultRow 4 m11CtxK.D m11OtK j =
      ⟨(Om j).lbl.size * 2 ^ 4, 2 ^ 4 / (OtD j).lbl.size, (Om j).lbl.size * 2 ^ 4⟩ := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold defaultRow
    rw [m11K_D_Om, Om_get hj', otD_get hj']
  rw [List.map_congr_left e]
  rfl

theorem m11K_overgroups {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M11))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m11Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  have hS : IsSylowTwoOf m11CtxK.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m11CtxK.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m11CtxK.S
    rw [m11CtxK.S_card, card_M11, m11K_k] at h1
    have h2 : m11CtxK.S.index = 495 := by omega
    rw [h2]
    norm_num
  have hall : ∀ Z : Subgroup G, m11CtxK.S ≤ Z → ∃ j ≤ 4, Z = memberOrTop 4 m11CtxK.Y j := by
    intro Z hZ
    obtain ⟨j, hj, rfl⟩ := m11CtxK.complete Z hZ
    rw [m11K_J] at hj ⊢
    exact ⟨j, hj, by simp⟩
  have hrows : ∀ j < 4, ∃ m ∈ m11Mems, MemStmt (m11CtxK.Y j) m := by
    intro j hj
    refine m11CtxK.rows_of_default (Ot := m11OtK) m11K_o2OK m11Mems ?_ j
      (by rw [m11K_J]; exact hj)
    rw [m11K_J, m11K_k]
    exact m11K_rows
  exact overgroups_of_lattice m11CtxK.S hS 4 m11CtxK.Y m11Mems hall hrows hX hT hTY

end CFSG.KD.M11Dc

end
