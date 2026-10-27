module

public import Certificates.Kernel.HSQuot.H
public import Certificates.Kernel.HSQuot.S1
public import Certificates.Kernel.HSQuot.S2
public import Certificates.Kernel.HSQuot.S3
public import Certificates.Kernel.LocalQT.HS4089.G
public import CFSG.Certificates.Kernel.LocalQTQuotSSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDcInputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
import all CFSG.Certificates.Kernel.LocalQTPcWSound
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 200000

public section

namespace CFSG.KD.HSQuot

open CFSG.KC.LQT.QS CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.QuasithinUnique.Vol2Native.L239.HSPairs
open CFSG.Sporadic.HS.Native (hsData)

theorem rep_pcw {c : Nat} {t : Array Nat} (h : CFSG.KC.LQT.PcW.Rep 1100 11 c t) :
    CFSG.KC.LQT.BW.Pf.Rep 1100 11 c t := by
  obtain ⟨hs, hg, -, hlt⟩ := h
  refine ⟨hs, fun i hi => ?_⟩
  have e : img t i = t[i]! := by
    rw [Array.getElem!_eq_getD]
    rfl
  have e2 : CFSG.KC.LQT.PW.imgW 11 c i = CFSG.KC.Enum.pg 11 (CFSG.KS.mask 11) c i := rfl
  rw [e, e2, hg i hi]
  exact ⟨hlt i hi, rfl⟩

theorem mt_eq {j : Nat} (hj : j < 5) :
    hsLatK.mt[j]! = (CFSG.KD.HSDc.J.mw.getD j []).map (wordTabA #[hsTa, hsTb] hsData.n) := by
  have hl : CFSG.KD.HSDc.J.mw.length = 5 := by rfl
  change (CFSG.KD.HSDc.J.mw.toArray.map _)[j]! = _
  rw [getElem!_pos _ j (by simp [hl, hj]), List.getD_eq_getElem _ _ (by omega)]
  simp

theorem letters1_eq : hsLatK.sTabs ++ hsLatK.mt[1]! = hsL1 := by
  rw [mt_eq (by norm_num)]
  have e : CFSG.KD.HSDc.J.mw.getD 1 [] = [hsW1] := by rfl
  rw [e]
  rfl

theorem letters2_eq : hsLatK.sTabs ++ hsLatK.mt[2]! = hsL2 := by
  rw [mt_eq (by norm_num)]
  have e : CFSG.KD.HSDc.J.mw.getD 2 [] = [hsW2] := by rfl
  rw [e]
  rfl

theorem rep1 : ∀ i < hsL1.length, CFSG.KC.LQT.BW.Pf.Rep 1100 11 (LC1.getD i 0) hsL1[i]! := by
  intro i hi
  rw [CFSG.KD.LQT.H4089.hlen1] at hi
  have h := rep_pcw (CFSG.KD.LQT.H4089.hL1 i hi)
  interval_cases i <;> exact h

theorem rep2 : ∀ i < hsL2.length, CFSG.KC.LQT.BW.Pf.Rep 1100 11 (LC2.getD i 0) hsL2[i]! := by
  intro i hi
  rw [CFSG.KD.LQT.H4089.hlen2] at hi
  have h := rep_pcw (CFSG.KD.LQT.H4089.hL2 i hi)
  interval_cases i <;> exact h

theorem entries1 : ∀ c < 15,
    setQ 11 hsB hsQuot1.length 18 RT1 3840 12 E1 PG1 (c * 256) 256 = true :=
  fun c hc => S1.all c hc

theorem entries2 : ∀ c < 42,
    setQ 11 hsB CFSG.Quasithin.A312Hs.hsQuot2.length 18 RT2 10752 14 E2 PG2 (c * 256) 256 =
      true := by
  intro c hc
  by_cases h : c < 21
  · exact S2.all c h
  · obtain ⟨r, rfl⟩ : ∃ r, c = r + 21 := ⟨c - 21, by omega⟩
    exact S3.all r (by omega : r < 21)

theorem quot1 :
    QuotOK hsData.n hsB (hsLatK.sTabs ++ hsLatK.mt[1]!) hsQuot1
      (bfsEnumB hsData.n hsB (hsQuot1.map (quotGt hsData.n (hsLatK.sTabs ++ hsLatK.mt[1]!)))
        (hsQuot1.map (quotGi hsData.n (hsLatK.sTabs ++ hsLatK.mt[1]!))) 1000000).1
      (bfsEnumB hsData.n hsB (hsQuot1.map (quotGt hsData.n (hsLatK.sTabs ++ hsLatK.mt[1]!)))
        (hsQuot1.map (quotGi hsData.n (hsLatK.sTabs ++ hsLatK.mt[1]!))) 1000000).2.1
      (bfsEnumB hsData.n hsB (hsQuot1.map (quotGt hsData.n (hsLatK.sTabs ++ hsLatK.mt[1]!)))
        (hsQuot1.map (quotGi hsData.n (hsLatK.sTabs ++ hsLatK.mt[1]!))) 1000000).2.2 3840 := by
  rw [letters1_eq]
  exact quotS_sound (n := 1100) (w := 11) (by norm_num) hsB hsL1 LC1 rfl rep1 hsQuot1 18 RT1 3840
    12 1000000 E1 PG1 15 256 3840 (by norm_num) hd1 entries1

theorem quot2 :
    QuotOK hsData.n hsB (hsLatK.sTabs ++ hsLatK.mt[2]!) CFSG.Quasithin.A312Hs.hsQuot2
      (bfsEnumB hsData.n hsB (CFSG.Quasithin.A312Hs.hsQuot2.map
          (quotGt hsData.n (hsLatK.sTabs ++ hsLatK.mt[2]!)))
        (CFSG.Quasithin.A312Hs.hsQuot2.map (quotGi hsData.n (hsLatK.sTabs ++ hsLatK.mt[2]!)))
        1000000).1
      (bfsEnumB hsData.n hsB (CFSG.Quasithin.A312Hs.hsQuot2.map
          (quotGt hsData.n (hsLatK.sTabs ++ hsLatK.mt[2]!)))
        (CFSG.Quasithin.A312Hs.hsQuot2.map (quotGi hsData.n (hsLatK.sTabs ++ hsLatK.mt[2]!)))
        1000000).2.1
      (bfsEnumB hsData.n hsB (CFSG.Quasithin.A312Hs.hsQuot2.map
          (quotGt hsData.n (hsLatK.sTabs ++ hsLatK.mt[2]!)))
        (CFSG.Quasithin.A312Hs.hsQuot2.map (quotGi hsData.n (hsLatK.sTabs ++ hsLatK.mt[2]!)))
        1000000).2.2 10752 := by
  rw [letters2_eq]
  exact quotS_sound (n := 1100) (w := 11) (by norm_num) hsB hsL2 LC2 rfl rep2
    CFSG.Quasithin.A312Hs.hsQuot2 18 RT2 10752 14 1000000 E2 PG2 42 256 10752 (by norm_num) hd2
    entries2

end CFSG.KD.HSQuot

end
