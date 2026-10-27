module

public import Certificates.Kernel.M23Dc.Final
public import Certificates.Kernel.M23Dc.OtChecks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.Certificates.Kernel.SporLatDcTupSound
public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGSporLat

@[expose] def OtD (j : Nat) : OmegaData (List (List Nat)) := tupLbl (Om j) (OtI j)

@[expose] def m23OtK : Array (OmegaData (List (List ℕ))) :=
  #[OtD 0, OtD 1, OtD 2, OtD 3, OtD 4, OtD 5, OtD 6, OtD 7, OtD 8, OtD 9, OtD 10, OtD 11, OtD 12,
    OtD 13, OtD 14, OtD 15]

theorem otD_get {j : ℕ} (hj : j < 16) : m23OtK[j]! = OtD j := by
  interval_cases j <;> rfl

theorem rowsB : (List.range 16).all (fun j => (Ps j).length == 3 &&
    ((oc j).2.1.take 3).all (fun r => r.all (· < 2 ^ 12) &&
      (oc j).1.flatten.length ≤ r.length) && (oc j).1.flatten.length % 2 == 1) = true := by
  quickRfl

theorem rows_get (rows : List (List ℕ)) (l k : ℕ) :
    (((rows.map List.toArray).toArray)[l]!)[k]! = (rows.getD l []).getD k 0 := by
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases rows[l]? with
  | none =>
    have e : (default : Array ℕ) = #[] := rfl
    simp [e]
  | some r =>
    simp only [Option.map_some, Option.getD_some, getElem!_def, List.getElem?_toArray]
    cases r[k]? <;> rfl

theorem pn_get (j l k : ℕ) : ((Om j).pn[l]!)[k]! = (((oc j).2.1).getD l []).getD k 0 :=
  rows_get _ l k

theorem Om_size (j : ℕ) : (Om j).lbl.size = (oc j).1.flatten.length := by
  change (oc j).1.flatten.toArray.size = _
  simp

theorem m23K_o2OK : O2OK (codeSetAct 23) m23LatK m23OtK := by
  refine ⟨by rw [mw_size]; rfl, fun j hj => ?_⟩
  have hj' : j < 16 := by rw [mw_size] at hj; exact hj
  have hB := List.all_eq_true.1 rowsB j (List.mem_range.2 hj')
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨hlen, hrows⟩, hodd⟩ := hB
  rw [Om_get hj', otD_get hj']
  refine ⟨by rw [Om_size]; exact hodd, ?_⟩
  have hs : m23LatK.sTabs.toArray = sT.toArray := by rw [T_eq.2.2]; rfl
  rw [hs]
  have hOm : OmegaSpec (codeSetAct 23) (mLet j) Δc (Om j) := by
    have e := (m23K_membersOK.2.2.2.2 j hj).2.2
    rwa [mLet_eq hj', delta_eq, Om_get hj'] at e
  have hsz : sT.toArray.size = 3 := rfl
  refine otIdxOK_sound (w := 12) (Ps := Ps j) (O := OtI j) hOm (fun l hl => ?_)
    (by rw [hlen]; rfl) (fun l hl k hk => ?_) (by rw [Om_size]; exact OT.all j hj')
  · rw [hsz] at hl
    have h3 : sT.length = 3 := rfl
    have hl' : l < (mLet j).size := by
      simp only [mLet, List.size_toArray, List.length_append]
      omega
    refine ⟨hl', ?_⟩
    rw [getElem!_pos _ l hl', getElem!_pos sT.toArray l (by rw [hsz]; exact hl)]
    simp only [mLet, List.getElem_toArray]
    exact List.getElem_append_left (by omega)
  · rw [hsz] at hl
    rw [Om_size] at hk
    have hl3 : l < ((oc j).2.1.take 3).length := by
      have e : (Ps j).length = ((oc j).2.1.take 3).length := List.length_map ..
      omega
    have ht : ((oc j).2.1.take 3).getD l [] = (oc j).2.1.getD l [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_take, hl]
    rw [pn_get, ← ht]
    exact codeK_rows (fun r hr x hx => (hrows r hr).1 x hx) (fun r hr => (hrows r hr).2) l hl3 k hk

theorem m23K_rows : (List.range 16).map (defaultRow 7 m23LatK m23OtK) = m23Mems := by
  have e : ∀ j ∈ List.range 16, defaultRow 7 m23LatK m23OtK j =
      ⟨(Om j).lbl.size * 2 ^ 7, 2 ^ 7 / (OtI j).lbl.size, (Om j).lbl.size * 2 ^ 7⟩ := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold defaultRow
    rw [Om_get hj', otD_get hj']
    simp only [OtD, tupLbl, Array.size_map]
  rw [List.map_congr_left e]
  rfl

open CFSG.QuasithinUnique
open CFSG.Sporadic.Schreier (m23_card)
open CFSG.Open (pCoreOf)


theorem m23K_D_o2OK : O2OK (codeSetAct 23) m23CtxK.D m23OtK := by
  unfold O2OK
  rw [m23K_D_mw, m23K_D_Om, (rfl : m23CtxK.D.sTabs = m23LatK.sTabs)]
  exact m23K_o2OK

theorem m23K_D_rows : (List.range 16).map (defaultRow 7 m23CtxK.D m23OtK) = m23Mems := by
  unfold defaultRow
  rw [m23K_D_Om]
  exact m23K_rows

theorem m23K_overgroups {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M23))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m23Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  have hS : IsSylowTwoOf m23CtxK.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m23CtxK.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m23CtxK.S
    have hk : m23CtxK.k = 7 := rfl
    rw [m23CtxK.S_card, m23_card, hk] at h1
    have h2 : m23CtxK.S.index = 79695 := by omega
    rw [h2]
    norm_num
  have hrows : ∀ j < 16, ∃ m ∈ m23Mems, MemStmt (m23CtxK.Y j) m := by
    intro j hj
    have hk : m23CtxK.k = 7 := rfl
    refine m23CtxK.rows_of_default (Ot := m23OtK) m23K_D_o2OK m23Mems ?_ j
      (by rw [m23K_J]; exact hj)
    rw [m23K_J, hk]
    exact m23K_D_rows
  exact overgroups_of_lattice m23CtxK.S hS 16 m23CtxK.Y m23Mems m23K_complete hrows hX hT hTY

end CFSG.KD.M23Dc

end
