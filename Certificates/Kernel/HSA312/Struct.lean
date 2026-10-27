module

public import Certificates.Kernel.HSA312.CI
public import Certificates.Kernel.HSA312.MV1
public import Certificates.Kernel.HSA312.MV2
public import Certificates.Kernel.LocalQT.HS4089.G
public import Certificates.Kernel.HSDc.Final
public import CFSG.Certificates.Kernel.HSA312Sound
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsKInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDc
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HSA312

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.PcW CFSG.KC.HSA312
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm (hsTa hsTb hsB)
open CFSG.Quasithin.A312Hs
open CFSG.Sporadic.HS.Native (hsData)

theorem n_eq : hsData.n = 1100 := rfl

theorem mw1 : CFSG.KD.HSDc.J.mw.getD 1 [] = [CFSG.QuasithinUnique.Vol2Native.L239.HSPairs.hsW1] := by
  decide

theorem mw2 : CFSG.KD.HSDc.J.mw.getD 2 [] = [CFSG.QuasithinUnique.Vol2Native.L239.HSPairs.hsW2] := by
  decide

theorem mt_eq {j : Nat} (hj : j < 5) :
    hsLatK.mt[j]! = (CFSG.KD.HSDc.J.mw.getD j []).map (wordTabA #[hsTa, hsTb] hsData.n) := by
  rw [HSK.mt_get CFSG.KD.HSDc.facts hj, HSK.mw_get]

theorem letters1 : hsLettersK 1 = CFSG.QuasithinUnique.Vol2Native.L239.HSPairs.hsL1 := by
  unfold hsLettersK
  rw [mt_eq (by decide), mw1]
  rfl

theorem letters2 : hsLettersK 2 = CFSG.QuasithinUnique.Vol2Native.L239.HSPairs.hsL2 := by
  unfold hsLettersK
  rw [mt_eq (by decide), mw2]
  rfl

theorem rep_ab_word {v : List Nat} (hv : ∀ l ∈ v, l < 2) :
    Rep 1100 11 (wordPB 1100 11 (mask 11) CFSG.KD.LQT.H4089.Lab v (CFSG.KD.LQT.H4089.TF 0))
      (wordTabA #[hsTa, hsTb] hsData.n v) := by
  rw [n_eq, wordTabA_foldr]
  exact rep_word (by norm_num) (by norm_num) CFSG.KD.LQT.H4089.rep_id0 v
    fun l hl => CFSG.KD.LQT.H4089.rep_ab l (hv l hl)

theorem incl_ok : inclPt hsDelta hsLatK 5 hsIncl = true := by
  rw [inclPt_iff]
  intro j hj jj hjj
  have hr : ∀ v ∈ CFSG.KD.HSDc.J.mw.getD j [], Rep 1100 11
      (wordPB 1100 11 (mask 11) CFSG.KD.LQT.H4089.Lab v (CFSG.KD.LQT.H4089.TF 0))
      (wordTabA #[hsTa, hsTb] hsData.n v) :=
    fun v hv => rep_ab_word (HSK.mw_lt2 CFSG.KD.HSDc.facts v hv)
  rw [gensIn_iff hr HSK.delta_lt (mt_eq hj), HSK.Om_get hjj]
  have hc := List.all_eq_true.1 (List.all_eq_true.1 incl j (List.mem_range.2 hj)) jj
    (List.mem_range.2 hjj)
  unfold inclB at hc
  rw [beq_iff_eq] at hc
  change gensInC 1100 11 (mask 11) _ _ _ _ _ = _ at hc
  rw [hc, List.contains_iff_mem, getElem!_pos hsIncl j (by change j < 5; exact hj),
    List.getD_eq_getElem _ _ (by change j < 5; exact hj)]

theorem hL1K : ∀ l < 4, Rep 1100 11 (CFSG.KD.LQT.H4089.L1c l) (hsLettersK 1)[l]! := by
  rw [letters1]
  exact CFSG.KD.LQT.H4089.hL1

theorem hL2K : ∀ l < 4, Rep 1100 11 (CFSG.KD.LQT.H4089.L2c l) (hsLettersK 2)[l]! := by
  rw [letters2]
  exact CFSG.KD.LQT.H4089.hL2

theorem len1 : (hsLettersK 1).length = 4 := by rw [letters1]; rfl

theorem len2 : (hsLettersK 2).length = 4 := by rw [letters2]; rfl

theorem expl1 : ExplOK hsData.n (hsLettersK 1) 64 hsV1Word hsV1Mul hsV1Conj := by
  rw [n_eq]
  exact explOK_of (by norm_num) (by norm_num) CFSG.KD.LQT.H4089.rep_id0 len1 hL1K v1W
    (fun i hi => CV1.all i hi) v1Dist (fun i hi => MV1.all i hi) v1Conj

theorem expl2 : ExplOK hsData.n (hsLettersK 2) 64 hsV2Word hsV2Mul hsV2Conj := by
  rw [n_eq]
  exact explOK_of (by norm_num) (by norm_num) CFSG.KD.LQT.H4089.rep_id0 len2 hL2K v2W
    (fun i hi => CV2.all i hi) v2Dist (fun i hi => MV2.all i hi) v2Conj

theorem struct : inclPt hsDelta hsLatK 5 hsIncl = true ∧
    ExplOK hsData.n (hsLettersK 1) 64 hsV1Word hsV1Mul hsV1Conj ∧
    ExplOK hsData.n (hsLettersK 2) 64 hsV2Word hsV2Mul hsV2Conj :=
  ⟨incl_ok, expl1, expl2⟩

end CFSG.KD.HSA312

end
