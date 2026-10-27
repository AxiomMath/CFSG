
module

public import Certificates.Kernel.J2Dc.IdxG
public import Certificates.Kernel.J2Dc.LatDCheck
public import Certificates.Data.J2T3K
public import Certificates.Data.J2Y9K
public import CFSG.Certificates.Kernel.S151IdxGAct
public import CFSG.Certificates.Kernel.SporLatDcSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.IdxG CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J2Lat
open CFSG.KC.LQT.PW

theorem latD_eq : j2LatD = j2LatK := by
  unfold j2LatD j2LatK
  rw [mw_eqD, om_eqD]
  rfl

theorem otD_get {j : ℕ} (hj : j < 5) : j2OtD[j]! = OtD j := by
  interval_cases j <;> rfl

theorem j2D_facts :
    LatFactsK (codeSetLab 315) 315 j2ta.toArray j2tb.toArray j2Delta
      (CFSG.Sporadic.J2.a : CFSG.Sporadic.J2.J) (CFSG.Sporadic.J2.b : CFSG.Sporadic.J2.J) j2Sg
      j2STabs j2LatD ∧
    j2LatD.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := by
  have e : j2SgK = j2Sg := rfl
  rw [latD_eq, ← e]
  exact ⟨⟨rfl, j2K_membersOK, j2K_stab, j2K_comp⟩, j2K_Om_size⟩

theorem o2OK : O2OK (codeSetAct 315) j2LatK j2OtD := by
  refine ⟨rfl, fun j hj => ?_⟩
  have hj' : j < 5 := hj
  rw [Om_get hj', otD_get hj']
  refine ⟨by interval_cases j <;> rfl, ?_⟩
  have hs : j2LatK.sTabs.toArray = sT.toArray := by rw [sT_eq]; rfl
  rw [hs]
  exact (omOKG_sound (act := tupAct (codeSetAct 315)) (letters := sT.toArray) (fun _ => True)
    trivial (fun l _ X _ => ⟨trivial, by
      unfold tupAct
      rw [codeSetAct_eq, Array.getElem!_eq_getD]
      rfl⟩)
    (List.all_eq_true.1 ot_ok j (List.mem_range.2 hj'))).1

theorem rows : (List.range 5).map (defaultRow 7 j2LatK j2OtD) = J2Y9K.mems := by
  have e : ∀ j ∈ List.range 5, defaultRow 7 j2LatK j2OtD j =
      ⟨(Om j).lbl.size * 2 ^ 7, 2 ^ 7 / (OtD j).lbl.size, (Om j).lbl.size * 2 ^ 7⟩ := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold defaultRow
    rw [Om_get hj', otD_get hj']
  rw [List.map_congr_left e]
  rfl

theorem gensIn_of {j jj : ℕ} (hj : j < 5) (hjj : jj < 5) (h : gensB j jj = true) :
    GensIn (codeSetAct 315) j2Delta j2LatK j jj := by
  intro t ht
  rw [mt_get hj, mw_get, List.mem_map] at ht
  obtain ⟨w, hw, rfl⟩ := ht
  rw [wordTabA_eq_L, ← T_eq.1, ← T_eq.2.1, delta_eq, codeSetAct_eq_codeSetF codesB
    (good_wW (mw_lt2 w hw)), Om_get hjj]
  have hm := List.all_eq_true.1 h w hw
  rw [List.contains_iff_mem, Array.mem_toList_iff, Array.mem_iff_getElem] at hm
  obtain ⟨x, hx, e⟩ := hm
  exact ⟨x, hx, by rw [getElem!_pos _ x hx, e]⟩

theorem notNormal_of {j : ℕ} (hj : j < 5) (h : nnB j = true) :
    ∃ ℓ ∈ (j2LatK.Om[j]!).lbl.toList, ∃ s ∈ j2LatK.sTabs, codeSetAct 315 s ℓ ≠ ℓ := by
  rw [Om_get hj, sT_eq]
  obtain ⟨ℓ, hℓ, hs⟩ := List.any_eq_true.1 h
  obtain ⟨s, hs, hne⟩ := List.any_eq_true.1 hs
  refine ⟨ℓ, hℓ, s, hs, ?_⟩
  rw [codeSetAct_eq]
  simpa using hne

theorem j2D_t3 : J2T3K.stmt := by
  unfold J2T3K.stmt J2T3K.notNormal J2T3K.incl
  rw [latD_eq]
  exact ⟨notNormal_of (by decide) nn4, gensIn_of (by decide) (by decide) gens13⟩

theorem j2D_y9 : J2Y9K.stmt := by
  unfold J2Y9K.stmt J2Y9K.rows J2Y9K.incl42 J2Y9K.incl13
  rw [latD_eq]
  exact ⟨⟨o2OK, rows⟩, gensIn_of (by decide) (by decide) gens42,
    gensIn_of (by decide) (by decide) gens13⟩

end CFSG.KD.J2Dc

end
