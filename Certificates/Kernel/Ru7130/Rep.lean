module

public import Certificates.Kernel.Ru7130.E8
public import Certificates.Kernel.LocalQT.Quot.F4080
public import CFSG.Certificates.Kernel.LocalQTPcWOfBW
public import CFSG.Certificates.Kernel.HSA312Sound
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 200000

public section

namespace CFSG.KD.Ru7130

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.PcW CFSG.KC.HSA312
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert CFSG.Quasithin.A312S.Ru
open CFSG.Sporadic.Ru.Native (ruData)

theorem hn : (4060 : Nat) < 2 ^ 32 := by norm_num

theorem hw : 0 < 12 := by norm_num

theorem hid : Rep 4060 12 I (idTab 4060) := rep_id (by norm_num) (by norm_num)

noncomputable abbrev T : Array (Array Nat) :=
  slpTabsA CFSG.KD.LQT.C4143.ta.toArray CFSG.KD.LQT.C4143.tb.toArray ruProg

theorem bw : T.size = 208 ∧ ∀ j < T.size, CFSG.KC.LQT.BW.Pf.Rep 4060 12 (CFSG.KD.LQT.C4143.TF j) T[j]! := by
  obtain ⟨hsz, hrep⟩ := CFSG.KC.LQT.BS.baseSK_rep (by norm_num) ruB CFSG.KD.LQT.C4143.ta
    CFSG.KD.LQT.C4143.tb ruProg ruQp CFSG.KD.LQT.C4143.TF 26 8 64 CFSG.KD.LQT.C4143.RT 154 187 191
    189 193 14 100000 16384 14 CFSG.KD.LQT.C4143.E 16 1024 CFSG.KD.LQT.C4143.hd
    CFSG.KD.LQT.C4143.N.all
  have hlen : ruProg.length = 206 := rfl
  rw [hlen] at hsz
  exact ⟨hsz, hrep⟩

theorem rTF {j : Nat} (hj : j < 208) : Rep 4060 12 (pcS 4060 12 4095 I (CFSG.KD.LQT.C4143.TF j)) T[j]! :=
  rep_of_bw hn hw hid (bw.2 j (by rw [bw.1]; exact hj))

theorem rLab : ∀ l < 2, Rep 4060 12 (Lab l)
    ((#[CFSG.KD.LQT.C4143.ta.toArray, CFSG.KD.LQT.C4143.tb.toArray] : Array (Array Nat)).getD l #[]) := by
  intro l hl
  have h0 := rTF (j := 0) (by norm_num)
  have h1 := rTF (j := 1) (by norm_num)
  unfold T slpTabsA at h0 h1
  rw [CFSG.KD.LQT.C4080.foldl_slpStepA_get _ _ (by simp)] at h0 h1
  interval_cases l
  · exact h0
  · exact h1

theorem rM : Rep 4060 12 M
    (wordTabA #[CFSG.KD.LQT.C4143.ta.toArray, CFSG.KD.LQT.C4143.tb.toArray] 4060 mw2) := by
  rw [wordTabA_foldr]
  exact rep_word hn hw hid mw2 fun l hl => rLab l (by simp [mw2] at hl; omega)

theorem quotL2_eq : ruQuotL2 = [T[163]!, T[172]!, T[185]!,
    wordTabA #[CFSG.KD.LQT.C4143.ta.toArray, CFSG.KD.LQT.C4143.tb.toArray] 4060 mw2] := by
  have e1 : ruTaL = ruTa := rfl
  have e2 : ruTbL = ruTb := rfl
  have e4 : ruMw[2]! = [mw2] := rfl
  have e5 : ruData.n = 4060 := rfl
  unfold ruQuotL2 ruSTabsL ruQpL
  rw [CFSG.KD.LQT.C4080.slpL_eq, e4, e5, e1, e2, CFSG.KD.LQT.C4143.ta_eq,
    CFSG.KD.LQT.C4143.tb_eq]
  rfl

theorem len2 : ruQuotL2.length = 4 := by rw [quotL2_eq]; rfl

theorem rL2 : ∀ l < ruQuotL2.length, Rep 4060 12 (Lc l) ruQuotL2[l]! := by
  rw [len2]
  intro l hl
  rw [quotL2_eq]
  interval_cases l
  · exact rTF (by norm_num)
  · exact rTF (by norm_num)
  · exact rTF (by norm_num)
  · exact rM

theorem rL2s : RepL 4060 12 Ls ruQuotL2.toArray.toList := by
  rw [List.toList_toArray]
  refine RepL.of_get (by rw [len2]; rfl) fun j hj => ?_
  have hj4 : j < 4 := by rwa [len2] at hj
  interval_cases j
  · exact rL2 0 hj
  · exact rL2 1 hj
  · exact rL2 2 hj
  · exact rL2 3 hj

theorem rV : RepL 4060 12 Vs ruVTabs.toList := by
  have e : ruVTabs.toList = ruVWords.map (wordTabA ruQuotL2.toArray 4060) := rfl
  have hl : ∀ v ∈ ruVWords, ∀ l ∈ v, l < ruQuotL2.length := by rw [len2]; decide
  have key : ∀ v ∈ ruVWords, Rep 4060 12 (wordPB 4060 12 4095 Lc v I)
      (wordTabA ruQuotL2.toArray 4060 v) := fun v hv => by
    rw [wordTabA_foldr]
    exact rep_word hn hw hid v (rep_letters rL2 (hl v hv))
  rw [e]
  refine ⟨by simp [Vs], fun j hj => ?_⟩
  have hj' : j < ruVWords.length := by simpa [Vs] using hj
  unfold Vs
  rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem _ _ (by simpa using hj'),
    List.getElem_map, List.getElem_map]
  exact key _ (List.getElem_mem _)

theorem e8Check_ru : CFSG.Quasithin.A312S.e8Check ruData.n ruVTabs ruQuotL2.toArray ruVMats = true :=
  e8_sound hn hw hid rV rfl rL2s e8

end CFSG.KD.Ru7130

end
