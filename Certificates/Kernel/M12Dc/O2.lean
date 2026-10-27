module

public import Certificates.Kernel.M12Dc.Final
public import Certificates.Kernel.M12Dc.OtChecks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KD.M12Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGSporLat

theorem otD_get {j : ℕ} (hj : j < 3) : m12OtK[j]! = OtD j := by
  interval_cases j <;> rfl

theorem m12K_o2OK : O2OK (codeSetAct 12) m12LatK m12OtK := by
  refine ⟨by rw [mw_size]; rfl, fun j hj => ?_⟩
  have hj' : j < 3 := by rw [mw_size] at hj; exact hj
  rw [Om_get hj', otD_get hj']
  refine ⟨by interval_cases j <;> rfl, ?_⟩
  have hs : m12LatK.sTabs.toArray = sT.toArray := by rw [T_eq.2.2]; rfl
  rw [hs]
  exact (omOKG_sound (act := tupAct (codeSetAct 12)) (letters := sT.toArray) (fun _ => True)
    trivial (fun l _ X _ => ⟨trivial, by
      unfold tupAct
      rw [codeSetAct_eq, Array.getElem!_eq_getD]
      rfl⟩)
    (List.all_eq_true.1 ots j (List.mem_range.2 hj'))).1

theorem m12K_rows : (List.range 3).map (defaultRow 6 m12LatK m12OtK) = m12Mems := by
  have e : ∀ j ∈ List.range 3, defaultRow 6 m12LatK m12OtK j =
      ⟨(Om j).lbl.size * 2 ^ 6, 2 ^ 6 / (OtD j).lbl.size, (Om j).lbl.size * 2 ^ 6⟩ := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold defaultRow
    rw [Om_get hj', otD_get hj']
  rw [List.map_congr_left e]
  rfl

open CFSG.QuasithinUnique
open CFSG.Sporadic.Mathieu (card_M12)
open CFSG.Open (pCoreOf)


theorem m12K_D_o2OK : O2OK (codeSetAct 12) m12CtxK.D m12OtK := by
  unfold O2OK
  rw [m12K_D_mw, m12K_D_Om, (rfl : m12CtxK.D.sTabs = m12LatK.sTabs)]
  exact m12K_o2OK

theorem m12K_D_rows : (List.range 3).map (defaultRow 6 m12CtxK.D m12OtK) = m12Mems := by
  unfold defaultRow
  rw [m12K_D_Om]
  exact m12K_rows

theorem m12K_overgroups {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M12))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m12Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  have hS : IsSylowTwoOf m12CtxK.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m12CtxK.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m12CtxK.S
    have hk : m12CtxK.k = 6 := rfl
    rw [m12CtxK.S_card, card_M12, hk] at h1
    have h2 : m12CtxK.S.index = 1485 := by omega
    rw [h2]
    norm_num
  have hrows : ∀ j < 3, ∃ m ∈ m12Mems, MemStmt (m12CtxK.Y j) m := by
    intro j hj
    have hk : m12CtxK.k = 6 := rfl
    refine m12CtxK.rows_of_default (Ot := m12OtK) m12K_D_o2OK m12Mems ?_ j
      (by rw [m12K_J]; exact hj)
    rw [m12K_J, hk]
    exact m12K_D_rows
  exact overgroups_of_lattice m12CtxK.S hS 3 m12CtxK.Y m12Mems m12K_complete hrows hX hT hTY

end CFSG.KD.M12Dc

end
