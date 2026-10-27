module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuY2Inputs
public import Certificates.Kernel.LocalQT.Quot.C4163
public import Certificates.Kernel.LocalQT.Quot.F4080
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuY2Inputs
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 200000

public section

namespace CFSG.KD.LQT.C4163

open CFSG.KC.LQT.QS CFSG.KC.LQT.BW.Pf CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.Ru
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert CFSG.Quasithin.A312Ru
open CFSG.Sporadic.Ru.Native (ruData)

theorem rep_tab_eq {n w c : Nat} {s t : Array Nat} (hs : Rep n w c s) (ht : Rep n w c t) :
    s = t := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  apply Array.ext (by rw [hs1, ht1])
  intro i hi1 hi2
  have hi : i < n := hs1 ▸ hi1
  have e : img s i = img t i := (hs2 i hi).2.symm.trans (ht2 i hi).2
  simpa [img, Array.getD_eq_getD_getElem?, hi1, hi2] using e

theorem quotL2_eq : ruQuotL2 =
    [(slpTabsA CFSG.KD.LQT.C4143.ta.toArray CFSG.KD.LQT.C4143.tb.toArray ruProg)[163]!,
     (slpTabsA CFSG.KD.LQT.C4143.ta.toArray CFSG.KD.LQT.C4143.tb.toArray ruProg)[172]!,
     (slpTabsA CFSG.KD.LQT.C4143.ta.toArray CFSG.KD.LQT.C4143.tb.toArray ruProg)[185]!,
     wordTabA #[CFSG.KD.LQT.C4143.ta.toArray, CFSG.KD.LQT.C4143.tb.toArray] 4060 mw2] := by
  have e1 : ruTaL = ruTa := rfl
  have e2 : ruTbL = ruTb := rfl
  have e4 : ruMw[2]! = [mw2] := rfl
  have e5 : ruData.n = 4060 := rfl
  unfold ruQuotL2 ruSTabsL ruQpL
  rw [CFSG.KD.LQT.C4080.slpL_eq, e4, e5, e1, e2, CFSG.KD.LQT.C4143.ta_eq,
    CFSG.KD.LQT.C4143.tb_eq]
  rfl

theorem letters_rep2 : ∀ i < 4, Rep 4060 12 (LC2.getD i 0) ruQuotL2.toArray[i]! := by
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
    rw [CFSG.KD.LQT.C4080.foldl_slpStepA_get _ _ (by simp)] at h0 h1
    interval_cases l
    · exact h0
    · exact h1
  rw [quotL2_eq]
  intro i hi
  rw [List.getElem!_toArray]
  interval_cases i
  · exact hrep 163 (by omega)
  · exact hrep 172 (by omega)
  · exact hrep 185 (by omega)
  · exact rep_wordTabA (n := 4060) (w := 12) (by norm_num) _ _ mw2 fun l hl => by
      have hl2 : l < 2 := by simp [mw2] at hl; omega
      exact ⟨by simpa using hl2, h01 l hl2⟩

theorem quot2_eq : ruQuot2 = xs2.map fun p => (⟨p.1, p.2.1, p.2.2⟩ : QuotGen) := rfl

theorem len2 : ruQuotL2.length = 4 := by rw [quotL2_eq]; rfl

theorem kGen' : KG.GC.length = 6 ∧
    (∀ i ∈ [0, 1, 2], KG.GC.getD i 0 = gC (xs2.getD i ([], 0, 0))) ∧
    ∀ i ∈ [0, 1, 2], KG.GC.getD (i + 3) 0 =
      powC 4060 12 (KG.GC.getD i 0) ((xs2.getD i ([], 0, 0)).2.2 - 1) := by
  have h := kGen
  simp only [Bool.and_eq_true, Nat.beq_eq, allL_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem rep_gt {x : List Nat × Nat × Nat} (hx : ∀ l ∈ x.1, l < 4) :
    Rep 4060 12 (gC x) (quotGt 4060 ruQuotL2 ⟨x.1, x.2.1, x.2.2⟩) := by
  unfold gC quotGt
  refine rep_powC (by norm_num) ?_ _
  exact rep_wordTabA (by norm_num) _ _ _ fun l hl =>
    ⟨by simpa [len2] using hx l hl, letters_rep2 l (hx l hl)⟩

theorem xs2_lt : ∀ i ∈ [0, 1, 2], ∀ l ∈ (xs2.getD i ([], 0, 0)).1, l < 4 := by decide

theorem rep_gi {i : Nat} (hi : i ∈ [0, 1, 2]) :
    Rep 4060 12 (KG.GC.getD i 0) (quotGt 4060 ruQuotL2
        ⟨(xs2.getD i ([], 0, 0)).1, (xs2.getD i ([], 0, 0)).2.1, (xs2.getD i ([], 0, 0)).2.2⟩) ∧
      Rep 4060 12 (KG.GC.getD (i + 3) 0) (quotGi 4060 ruQuotL2
        ⟨(xs2.getD i ([], 0, 0)).1, (xs2.getD i ([], 0, 0)).2.1, (xs2.getD i ([], 0, 0)).2.2⟩) := by
  have h1 : Rep 4060 12 (KG.GC.getD i 0) _ := (kGen'.2.1 i hi) ▸ rep_gt (xs2_lt i hi)
  refine ⟨h1, ?_⟩
  rw [kGen'.2.2 i hi]
  unfold quotGi
  exact rep_powC (by norm_num) h1 _

theorem odd_ok : OddGenOK ruData.n ruQuotL2 ruQuot2 ruQuot2Words := by
  have e5 : ruData.n = 4060 := rfl
  have hO := kOdd
  have hW := kWords
  rw [allL_eq, List.all_eq_true] at hO hW
  unfold OddGenOK
  rw [e5, len2, quot2_eq]
  refine ⟨?_, rfl, by decide, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ : ∃ i ∈ [0, 1, 2], xs2.getD i ([], 0, 0) = p := by
      simp only [xs2, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
    have hm : ∀ i ∈ [0, 1, 2], (xs2.getD i ([], 0, 0)).2.2 % 2 = 1 := by decide
    refine ⟨xs2_lt i hi, hm i hi, ?_⟩
    have hr := rep_powC (by norm_num) (rep_gi hi).1 (xs2.getD i ([], 0, 0)).2.2
    rw [Nat.eq_of_beq_eq_true (hO i hi)] at hr
    exact rep_tab_eq hr (rep_oneW (by norm_num))
  · intro j hj
    have hj' : j ∈ [0, 1, 2, 3] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hrw : Rep 4060 12 (wordC 4060 12 KG.GC (ws2.getD j []))
        (wordTabA ((xs2.map fun p => (⟨p.1, p.2.1, p.2.2⟩ : QuotGen)).map (quotGt 4060 ruQuotL2) ++
          (xs2.map fun p => (⟨p.1, p.2.1, p.2.2⟩ : QuotGen)).map (quotGi 4060 ruQuotL2)).toArray
          4060 (ws2.getD j [])) := by
      refine rep_wordTabA (by norm_num) _ _ _ fun l hl => ?_
      have hl6 : l < 6 := by
        have : ∀ j ∈ [0, 1, 2, 3], ∀ l ∈ ws2.getD j [], l < 6 := by decide
        exact this j hj' l hl
      refine ⟨by simp only [List.size_toArray, List.length_append, List.length_map]; exact hl6, ?_⟩
      rw [List.getElem!_toArray]
      have hl6' : l ∈ [0, 1, 2, 3, 4, 5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl6'
      rcases hl6' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (rep_gi (i := 0) (by decide)).1
      · exact (rep_gi (i := 1) (by decide)).1
      · exact (rep_gi (i := 2) (by decide)).1
      · exact (rep_gi (i := 0) (by decide)).2
      · exact (rep_gi (i := 1) (by decide)).2
      · exact (rep_gi (i := 2) (by decide)).2
    rw [Nat.eq_of_beq_eq_true (hW j hj')] at hrw
    have hl := letters_rep2 j hj
    rw [List.getElem!_toArray] at hl
    have e : ruQuot2Words = ws2 := rfl
    have e2 : ∀ j < 4, ws2[j]! = ws2.getD j [] := by decide
    rw [e, e2 j hj]
    exact rep_tab_eq hrw hl

end CFSG.KD.LQT.C4163

end
