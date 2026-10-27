module

public import Certificates.Kernel.M22Dc.Final
public import Certificates.Kernel.M22Dc.OtChecks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KD.M22Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGSporLat

theorem otD_get {j : ℕ} (hj : j < 5) : m22OtK[j]! = OtD j := by
  interval_cases j <;> rfl

theorem m22K_o2OK : O2OK (codeSetAct 22) m22LatK m22OtK := by
  refine ⟨by rw [mw_size]; rfl, fun j hj => ?_⟩
  have hj' : j < 5 := by rw [mw_size] at hj; exact hj
  rw [Om_get hj', otD_get hj']
  refine ⟨by interval_cases j <;> rfl, ?_⟩
  have hs : m22LatK.sTabs.toArray = sT.toArray := by rw [T_eq.2.2]; rfl
  rw [hs]
  exact (omOKG_sound (act := tupAct (codeSetAct 22)) (letters := sT.toArray) (fun _ => True)
    trivial (fun l _ X _ => ⟨trivial, by
      unfold tupAct
      rw [codeSetAct_eq, Array.getElem!_eq_getD]
      rfl⟩)
    (List.all_eq_true.1 ots j (List.mem_range.2 hj'))).1

theorem m22K_rows : (List.range 5).map (defaultRow 7 m22LatK m22OtK) = m22Mems := by
  have e : ∀ j ∈ List.range 5, defaultRow 7 m22LatK m22OtK j =
      ⟨(Om j).lbl.size * 2 ^ 7, 2 ^ 7 / (OtD j).lbl.size, (Om j).lbl.size * 2 ^ 7⟩ := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold defaultRow
    rw [Om_get hj', otD_get hj']
  rw [List.map_congr_left e]
  rfl

open CFSG.QuasithinUnique
open CFSG.Sporadic.Mathieu (card_M22)
open CFSG.Open (pCoreOf)


theorem m22K_D_o2OK : O2OK (codeSetAct 22) m22CtxK.D m22OtK := by
  unfold O2OK
  rw [m22K_D_mw, m22K_D_Om, (rfl : m22CtxK.D.sTabs = m22LatK.sTabs)]
  exact m22K_o2OK

theorem m22K_D_rows : (List.range 5).map (defaultRow 7 m22CtxK.D m22OtK) = m22Mems := by
  unfold defaultRow
  rw [m22K_D_Om]
  exact m22K_rows

theorem m22K_overgroups {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M22))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m22Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  have hS : IsSylowTwoOf m22CtxK.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m22CtxK.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m22CtxK.S
    have hk : m22CtxK.k = 7 := rfl
    rw [m22CtxK.S_card, card_M22, hk] at h1
    have h2 : m22CtxK.S.index = 3465 := by omega
    rw [h2]
    norm_num
  have hrows : ∀ j < 5, ∃ m ∈ m22Mems, MemStmt (m22CtxK.Y j) m := by
    intro j hj
    have hk : m22CtxK.k = 7 := rfl
    refine m22CtxK.rows_of_default (Ot := m22OtK) m22K_D_o2OK m22Mems ?_ j
      (by rw [m22K_J]; exact hj)
    rw [m22K_J, hk]
    exact m22K_D_rows
  exact overgroups_of_lattice m22CtxK.S hS 5 m22CtxK.Y m22Mems m22K_complete hrows hX hT hTY

end CFSG.KD.M22Dc

end
