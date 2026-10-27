module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuInputs
public import Certificates.Kernel.LocalQT.Quot.C4080H
public import Certificates.Kernel.LocalQT.Quot.C4080S0
public import Certificates.Kernel.LocalQT.Quot.C4080S1
public import Certificates.Kernel.LocalQT.Quot.C4080S2
public import Certificates.Kernel.LocalQT.Quot.C4080S3
public import Certificates.Kernel.LocalQT.Quot.C4080S4
public import Certificates.Kernel.LocalQT.Quot.C4080S5
public import Certificates.Kernel.LocalQT.Quot.C4080S6
public import Certificates.Kernel.LocalQT.Quot.C4080S7
public import Certificates.Kernel.LocalQT.Base.C4143
public import CFSG.Certificates.Kernel.LocalQTQuotSSound
public import CFSG.Certificates.Kernel.LocalQTBaseSRep

set_option maxRecDepth 200000

public section

namespace CFSG.KD.LQT.C4080

open CFSG.KC.LQT.QS CFSG.KC.LQT.BW.Pf CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.Ru
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.Sporadic.Ru.Native (ruData)

theorem foldl_slpStepA_get {i : Nat} : ∀ (l : List (Nat × Nat)) (arr : Array (Array Nat)),
    i < arr.size → (l.foldl slpStepA arr)[i]! = arr[i]!
  | [], _, _ => rfl
  | p :: l, arr, h => by
    have hs : i < (slpStepA arr p).size := by simp [slpStepA]; omega
    rw [List.foldl_cons, foldl_slpStepA_get l _ hs, getElem!_pos (slpStepA arr p) i hs,
      getElem!_pos arr i h]
    simp [slpStepA, Array.getElem_push_lt h]

theorem slpL_eq : ruSLPL = slpTabsA CFSG.KD.LQT.C4143.ta.toArray CFSG.KD.LQT.C4143.tb.toArray ruProg := by
  have e1 : ruTaL = ruTa := rfl
  have e2 : ruTbL = ruTb := rfl
  have e3 : ruProgL = ruProg := rfl
  unfold ruSLPL
  rw [e1, e2, e3, CFSG.KD.LQT.C4143.ta_eq, CFSG.KD.LQT.C4143.tb_eq]

theorem quotL1_eq : ruQuotL1 =
    [(slpTabsA CFSG.KD.LQT.C4143.ta.toArray CFSG.KD.LQT.C4143.tb.toArray ruProg)[163]!,
     (slpTabsA CFSG.KD.LQT.C4143.ta.toArray CFSG.KD.LQT.C4143.tb.toArray ruProg)[172]!,
     (slpTabsA CFSG.KD.LQT.C4143.ta.toArray CFSG.KD.LQT.C4143.tb.toArray ruProg)[185]!,
     wordTabA #[CFSG.KD.LQT.C4143.ta.toArray, CFSG.KD.LQT.C4143.tb.toArray] 4060 mw] := by
  have e1 : ruTaL = ruTa := rfl
  have e2 : ruTbL = ruTb := rfl
  have e4 : ruMw[1]! = [mw] := rfl
  have e5 : ruData.n = 4060 := rfl
  unfold ruQuotL1 ruSTabsL ruQpL
  rw [slpL_eq, e4, e5, e1, e2, CFSG.KD.LQT.C4143.ta_eq, CFSG.KD.LQT.C4143.tb_eq]
  rfl

theorem letters_rep : ∀ i < ruQuotL1.length, Rep 4060 12 (LC.getD i 0) ruQuotL1[i]! := by
  have hR := CFSG.KC.LQT.BS.baseSK_rep (by norm_num) ruB CFSG.KD.LQT.C4143.ta
    CFSG.KD.LQT.C4143.tb ruProg ruQp CFSG.KD.LQT.C4143.TF 26 8 64 CFSG.KD.LQT.C4143.RT 154 187 191
    189 193 14 100000 16384 14 CFSG.KD.LQT.C4143.E 16 1024 CFSG.KD.LQT.C4143.hd
    CFSG.KD.LQT.C4143.N.all
  obtain ⟨hsz, hrep⟩ := hR
  have hlen : ruProg.length = 206 := rfl
  rw [hlen] at hsz
  have h01 : ∀ l < 2, Rep 4060 12 ([CFSG.KD.LQT.C4143.TF 0, CFSG.KD.LQT.C4143.TF 1].getD l 0)
      (#[CFSG.KD.LQT.C4143.ta.toArray, CFSG.KD.LQT.C4143.tb.toArray] : Array (Array Nat))[l]! := by
    intro l hl
    have h0 := hrep 0 (by omega)
    have h1 := hrep 1 (by omega)
    unfold slpTabsA at h0 h1
    rw [foldl_slpStepA_get _ _ (by simp)] at h0 h1
    interval_cases l
    · exact h0
    · exact h1
  rw [quotL1_eq]
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  · exact hrep 163 (by omega)
  · exact hrep 172 (by omega)
  · exact hrep 185 (by omega)
  · exact rep_wordTabA (n := 4060) (w := 12) (by norm_num) _ _ mw fun l hl => by
      have hl2 : l < 2 := by simp [mw] at hl; omega
      exact ⟨by simpa using hl2, h01 l hl2⟩

theorem entries : ∀ c < 120,
    setQ 12 ruB ruQuot1.length 64 RT 122880 17 E PG (c * 1024) 1024 = true := by
  intro c hc
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 15 ∧ c = r + 15 * q :=
    ⟨c / 15, c % 15, Nat.mod_lt _ (by norm_num), by omega⟩
  have hq : q < 8 := by omega
  interval_cases q
  · exact S0.all r hr
  · exact S1.all r hr
  · exact S2.all r hr
  · exact S3.all r hr
  · exact S4.all r hr
  · exact S5.all r hr
  · exact S6.all r hr
  · exact S7.all r hr

theorem quot_cert :
    QuotOK ruData.n ruB ruQuotL1 ruQuot1 ruQuotEnum.1 ruQuotEnum.2.1 ruQuotEnum.2.2 122880 :=
  quotS_sound (n := 4060) (w := 12) (by norm_num) ruB ruQuotL1 LC rfl letters_rep ruQuot1 64 RT
    122880 17 1000000 E PG 120 1024 122880 (by norm_num) hd entries

end CFSG.KD.LQT.C4080

end
