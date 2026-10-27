module

public import Certificates.Kernel.E68Spor4214.J2
public import Certificates.Kernel.E68Spor4214.HS
public import Certificates.Kernel.J2Dc.Nodes
public import Certificates.Kernel.LocalQT.HS4089.G
public import CFSG.Certificates.Kernel.E68SporClassSound
public import CFSG.Certificates.Kernel.SporLatCodeRSound
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import Certificates.Data.E68Spor.Chk
import all CFSG.Certificates.Kernel.LocalQTPcWSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.E68S4214

open CFSG.KC.SLOrb CFSG.KC.SLOm CFSG.KC.E64F CFSG.Quasithin.E6.Spor
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.HS.Native (hsData)

theorem j2_ta : J2.ta = CFSG.KD.LQT.C4142.ta := rfl

theorem j2_tb : J2.tb = CFSG.KD.LQT.C4142.tb := rfl

theorem j2_R : J2.R = CFSG.KD.J2Dc.R := rfl

theorem slp_get (l : List (Nat × Nat)) (arr : Array (Array Nat)) (i : Nat) (hi : i < arr.size) :
    (l.foldl slpStepA arr)[i]! = arr[i]! := by
  induction l generalizing arr with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldl_cons, ih _ (by simp [slpStepA]; omega)]
    unfold slpStepA
    rw [getElem!_pos (arr.push _) i (by simp; omega), getElem!_pos arr i hi,
      Array.getElem_push_lt hi]

theorem j2_slp0 : j2SLP[0]! = j2ta.toArray := by
  unfold j2SLP slpTabsA
  rw [slp_get j2Prog _ 0 (by simp)]
  rfl

theorem j2_slp1 : j2SLP[1]! = j2tb.toArray := by
  unfold j2SLP slpTabsA
  rw [slp_get j2Prog _ 1 (by simp)]
  rfl

theorem j2_good {j : Nat} (hj : j < j2Prog.length + 2) : Good 315 j2SLP[j]! (J2.N j) := by
  have h := CFSG.KD.J2Dc.rep_good (CFSG.KD.J2Dc.rep_node hj)
  rw [← CFSG.KD.J2Dc.slp_lit, ← j2_R] at h
  exact h

theorem j2_zT : J2.zT = j2SLP[143]! := by
  rw [CFSG.KD.J2Dc.node_arr (by decide), ← j2_R]
  rfl

theorem j2_sTabs : CFSG.Quasithin.E2P.SporB.J2Lat.j2STabs = [j2SLP[155]!, j2SLP[166]!, j2SLP[179]!] :=
  rfl

theorem j2_delta : CFSG.Quasithin.E2P.SporB.J2Lat.j2Delta = J2.D := by
  rw [CFSG.Quasithin.E2P.SporB.J2Lat.j2Delta, sortN_eq]
  rfl

theorem j2_ok : classChk 315 j2ta.toArray j2tb.toArray j2SLP[143]! 315 = true ∧
    rChk 315 (codeSetAct 315) CFSG.Quasithin.E2P.SporB.J2Lat.j2Delta
      CFSG.Quasithin.E2P.SporB.J2Lat.j2STabs j2ta.toArray j2tb.toArray j2SLP[143]!
      j2UWords j2YWord j2NWord 5 15 = true := by
  have ht := J2.tab_ok
  have ho := J2.orb_ok
  have hr := J2.r_ok
  rw [Bool.and_eq_true] at ht
  rw [j2_zT, j2_ta, j2_tb, ← CFSG.KD.LQT.C4142.ta_eq, ← CFSG.KD.LQT.C4142.tb_eq] at ht ho
  have ha : Good 315 j2ta.toArray (J2.AB 0) := by
    have h := j2_good (j := 0) (by decide)
    rw [j2_slp0] at h
    exact h
  have hb : Good 315 j2tb.toArray (J2.AB 1) := by
    have h := j2_good (j := 1) (by decide)
    rw [j2_slp1] at h
    exact h
  have hz : Good 315 j2SLP[143]! (J2.N 143) := j2_good (by decide)
  have hS : ∀ l < CFSG.Quasithin.E2P.SporB.J2Lat.j2STabs.length,
      Good 315 (CFSG.Quasithin.E2P.SporB.J2Lat.j2STabs.toArray.getD l #[]) (J2.L l) := by
    rw [j2_sTabs]
    intro l hl
    rcases l with _ | _ | _ | l
    · exact j2_good (by decide)
    · exact j2_good (by decide)
    · exact j2_good (by decide)
    · exact absurd hl (by simp)
  have h3 : CFSG.Quasithin.E2P.SporB.J2Lat.j2STabs.length = 3 := by
    rw [j2_sTabs]
    rfl
  rw [← h3, ← j2_delta] at hr
  exact ⟨classChk_of_tab (by decide) ht.1 ht.2 ho, rChkC_sound hS ha hb hz hr⟩

theorem hs_good {n w c : Nat} {t : Array Nat} (h : CFSG.KC.LQT.PcW.Rep n w c t) :
    Good n t (CFSG.KC.LQT.PW.imgW w c) :=
  ⟨h.1, fun p hp => by
    have hp' : p < t.size := by rw [h.1]; exact hp
    have e := h.2.1 p hp
    rw [getElem!_pos t p hp'] at e
    refine ⟨?_, h.2.2.2 p hp⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp', Option.getD_some, e]
    rfl⟩

theorem hs_node {j : Nat} (hj : j < 219) :
    Good 1100 hsSLP[j]! (CFSG.KC.LQT.PW.imgW 11 (CFSG.KD.LQT.H4089S.TF j)) :=
  hs_good (CFSG.KD.LQT.H4089.rep_nodes j hj)

theorem hs_sTabs : HS.hsSTabs = [hsSLP[172]!, hsSLP[185]!, hsSLP[200]!] := rfl

theorem hs_ok : rChk hsData.n ptAct HS.hsDelta HS.hsSTabs hsTa hsTb hsSLP[164]! hsUWords hsYWord
      hsNWord 5 15 = true ∧ ncChk hsData.n hsTa hsSLP[164]! = true := by
  have hn : (hsData ()).n = 1100 := rfl
  have ha : Good 1100 hsTa (HS.AB 0) := hs_good CFSG.KD.LQT.H4089.rep_ta
  have hb : Good 1100 hsTb (HS.AB 1) := hs_good CFSG.KD.LQT.H4089.rep_tb
  have hz : Good 1100 hsSLP[164]! HS.Z := hs_node (by decide)
  have hS : ∀ l < HS.hsSTabs.length, Good 1100 (HS.hsSTabs.toArray.getD l #[]) (HS.L l) := by
    rw [hs_sTabs]
    intro l hl
    rcases l with _ | _ | _ | l
    · exact hs_node (by decide)
    · exact hs_node (by decide)
    · exact hs_node (by decide)
    · exact absurd hl (by simp)
  have h3 : HS.hsSTabs.length = 3 := by
    rw [hs_sTabs]
    rfl
  have hr := HS.r_ok
  rw [← h3] at hr
  rw [hn]
  exact ⟨rChkF_sound hS ha hb hz hr, ncChkF_sound ha hz HS.nc_ok⟩

end CFSG.KD.E68S4214

end
