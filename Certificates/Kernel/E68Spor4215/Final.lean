module

public import Certificates.Kernel.E68Spor4215.He
public import Certificates.Kernel.E68Spor4215.Ru
public import Certificates.Kernel.He7149.Final
public import Certificates.Kernel.LocalQT.Base.C4143
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import Certificates.Data.E68Spor.Chk

set_option maxRecDepth 100000

public section

namespace CFSG.KD.E68S4215

open CFSG.KC.E64F CFSG.KC.SLOm CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.BW.Pf
open CFSG.Sporadic.Ru.Native (ruData)

theorem good_he {j : Nat} (hj : j < heProg.length + 2) :
    Good 8330 heSLP[j]! (CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF j)) :=
  CFSG.KD.He7149.good_of_rep (CFSG.KD.He7149.rep_he hj)

theorem slp_get01 (ta tb : Array Nat) (prog : List (Nat × Nat)) :
    (slpTabsA ta tb prog)[0]! = ta ∧ (slpTabsA ta tb prog)[1]! = tb := by
  unfold slpTabsA
  rw [CFSG.KD.He7149.slp_get prog _ 0 (by simp), CFSG.KD.He7149.slp_get prog _ 1 (by simp)]
  exact ⟨rfl, rfl⟩

theorem he_sTabs : He.heSTabsC = [heSLP[197]!, heSLP[207]!, heSLP[226]!, heSLP[247]!] := by
  have hq : He.heQpC = heQp := rfl
  unfold He.heSTabsC
  rw [CFSG.KD.He7149.hSLPC, hq]
  rfl

theorem he_ok : rChk 8330 ptAct He.heDelta He.heSTabsC heTa heTb He.heSLPC[170]! heUWords heYWord
      heNWord 7 21 = true ∧ ncChk 8330 heTa He.heSLPC[170]! = true := by
  have ha : Good 8330 heTa (He.AB 0) := by
    have h := good_he (j := 0) (by decide)
    unfold heSLP at h
    rw [(slp_get01 heTa heTb heProg).1] at h
    exact h
  have hb : Good 8330 heTb (He.AB 1) := by
    have h := good_he (j := 1) (by decide)
    unfold heSLP at h
    rw [(slp_get01 heTa heTb heProg).2] at h
    exact h
  have hz : Good 8330 He.heSLPC[170]! He.Z := by
    rw [CFSG.KD.He7149.hSLPC]
    exact good_he (by decide)
  have hS : ∀ l < He.heSTabsC.length, Good 8330 (He.heSTabsC.toArray.getD l #[]) (He.L l) := by
    rw [he_sTabs]
    intro l hl
    rcases l with _ | _ | _ | _ | l
    · exact good_he (by decide)
    · exact good_he (by decide)
    · exact good_he (by decide)
    · exact good_he (by decide)
    · exact absurd hl (by simp)
  have h4 : He.heSTabsC.length = 4 := by
    rw [he_sTabs]
    rfl
  have hr := He.r_ok
  rw [← h4] at hr
  exact ⟨rChkF_sound hS ha hb hz hr, ncChkF_sound ha hz He.nc_ok⟩

theorem rep_ru {j : Nat} (hj : j < ruProg.length + 2) :
    Rep 4060 12 (CFSG.KD.LQT.C4143.TF j) ruSLP[j]! := by
  have h := CFSG.KC.LQT.BS.baseSK_rep (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    CFSG.KD.LQT.C4143.hd CFSG.KD.LQT.C4143.N.all
  unfold ruSLP
  rw [CFSG.KD.LQT.C4143.ta_eq, CFSG.KD.LQT.C4143.tb_eq]
  exact h.2 j (by rw [h.1]; exact hj)

theorem good_ru {j : Nat} (hj : j < ruProg.length + 2) :
    Good 4060 ruSLP[j]! (CFSG.KC.LQT.PW.imgW 12 (CFSG.KD.LQT.C4143.TF j)) :=
  CFSG.KD.He7149.good_of_rep (rep_ru hj)

theorem ru_SLPL : RuCert.ruSLPL = ruSLP := by
  have hp : RuCert.ruProgL = ruProg := by decide
  have ha : RuCert.ruTaL = ruTa := rfl
  have hb : RuCert.ruTbL = ruTb := rfl
  unfold RuCert.ruSLPL ruSLP
  rw [hp, ha, hb]

theorem ru_sTabs : RuCert.ruSTabsL = [ruSLP[163]!, ruSLP[172]!, ruSLP[185]!] := by
  have hq : RuCert.ruQpL = ruQp := rfl
  unfold RuCert.ruSTabsL
  rw [ru_SLPL, hq]
  rfl

theorem ru_ok : rChk ruData.n ptAct RuCert.ruDelta RuCert.ruSTabsL RuCert.ruTaL RuCert.ruTbL
      RuCert.ruSLPL[154]! ruUWords ruYWord ruNWord 5 15 = true ∧
    ncChk ruData.n RuCert.ruTaL RuCert.ruSLPL[154]! = true := by
  have hn : (ruData ()).n = 4060 := rfl
  have ha : Good 4060 RuCert.ruTaL (Ru.AB 0) := by
    have h := good_ru (j := 0) (by decide)
    unfold ruSLP at h
    rw [(slp_get01 ruTa ruTb ruProg).1] at h
    exact h
  have hb : Good 4060 RuCert.ruTbL (Ru.AB 1) := by
    have h := good_ru (j := 1) (by decide)
    unfold ruSLP at h
    rw [(slp_get01 ruTa ruTb ruProg).2] at h
    exact h
  have hz : Good 4060 RuCert.ruSLPL[154]! Ru.Z := by
    rw [ru_SLPL]
    exact good_ru (by decide)
  have hS : ∀ l < RuCert.ruSTabsL.length, Good 4060 (RuCert.ruSTabsL.toArray.getD l #[]) (Ru.L l) := by
    rw [ru_sTabs]
    intro l hl
    rcases l with _ | _ | _ | l
    · exact good_ru (by decide)
    · exact good_ru (by decide)
    · exact good_ru (by decide)
    · exact absurd hl (by simp)
  have h3 : RuCert.ruSTabsL.length = 3 := by
    rw [ru_sTabs]
    rfl
  have hr := Ru.r_ok
  rw [← h3] at hr
  rw [hn]
  exact ⟨rChkF_sound hS ha hb hz hr, ncChkF_sound ha hz Ru.nc_ok⟩

end CFSG.KD.E68S4215

end
