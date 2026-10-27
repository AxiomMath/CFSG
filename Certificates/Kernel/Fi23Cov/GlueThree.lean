module

public import Certificates.Kernel.Fi23Cov.Words
public import Certificates.Kernel.Fi23Cov.ThreeH
public import Certificates.Kernel.Fi23Cov.ThreeS
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPath
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTwoCent
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Kernel.SporCovBase.Fi22Glue
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Walter.JRFacts
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620Base
public import Certificates.Certificate13622Base

public section

namespace CFSG.KD.Fi23Cov

#kc_forall_tree r_all (fun i => CFSG.KD.Fi23Cov.rep i = true) 4 CFSG.KD.Fi23Cov.Ck.r
#kc_forall_tree cL_all (fun j => CFSG.KD.Fi23Cov.cL j = true) 8 CFSG.KD.Fi23Cov.Ck.cL
#kc_forall_tree dL_all (fun j => CFSG.KD.Fi23Cov.dL j = true) 8 CFSG.KD.Fi23Cov.Ck.dL
#kc_forall_tree cS_all (fun k => CFSG.KD.Fi23Cov.cS k = true) 13 CFSG.KD.Fi23Cov.Ck.cS
#kc_forall_tree dS_all (fun k => CFSG.KD.Fi23Cov.dS k = true) 10 CFSG.KD.Fi23Cov.Ck.dS

open CFSG.KC.Fi23Cov CFSG.Sporadic.Fi23 CFSG.StandardType.SporadicShape
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
open CFSG.Sporadic.Bridge.Fi23 (img)

theorem ok39 : okW [39] := okW_lit (by decide)

theorem ok40 : okW [40] := okW_lit (by decide)

theorem ok41 : okW [41] := okW_lit (by decide)


theorem a_mul_a : a * a = 1 := by
  rw [mul_eq_one_iff_eq_inv, a_inv]

theorem isConj_of_conj {t g x : J} (h : t * g = g * x) : IsConj t x :=
  isConj_iff.2 ⟨g⁻¹, by rw [inv_inv, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]⟩

theorem wJ_t3W : ∀ i : Fin 4, wJ (nthW t3W i) = t3 i := by
  intro i
  fin_cases i
  · change wJ [3, 2] = img 2 * img 3
    simp only [wJ_cons, wJ_nil, one_mul, jL_img (by norm_num : (2 : ℕ) < 10),
      jL_img (by norm_num : (3 : ℕ) < 10)]
  · have e : nthW t3W 1 =
        (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native.kleinZ.reverse).map (52 + ·) :=
      rfl
    change wJ (nthW t3W 1) = zJ
    rw [e, wJ_chain]
    rfl
  · change wJ [1, 2, 5, 4] = img 4 * img 5 * img 2 * img 1
    simp only [wJ_cons, wJ_nil, one_mul, jL_img (by norm_num : (1 : ℕ) < 10),
      jL_img (by norm_num : (2 : ℕ) < 10), jL_img (by norm_num : (4 : ℕ) < 10),
      jL_img (by norm_num : (5 : ℕ) < 10)]
  · change wJ [1, 6, 0, 7, 3, 5] =
      img 5 * img 3 * img 7 * img 0 * img 6 * img 1
    simp only [wJ_cons, wJ_nil, one_mul, jL_img (by norm_num : (0 : ℕ) < 10),
      jL_img (by norm_num : (1 : ℕ) < 10), jL_img (by norm_num : (3 : ℕ) < 10),
      jL_img (by norm_num : (5 : ℕ) < 10), jL_img (by norm_num : (6 : ℕ) < 10),
      jL_img (by norm_num : (7 : ℕ) < 10)]

theorem okW_t3W (i : ℕ) : okW (nthW t3W i) := by
  rcases i with _ | _ | _ | _ | i
  · exact okW_lit (by decide)
  · exact okW_lit (by decide)
  · exact okW_lit (by decide)
  · exact okW_lit (by decide)
  · have hl : t3W.length = 4 := rfl
    rw [nthW_ge t3W (i + 4) (by omega)]
    exact okW_nil


theorem rep_facts (i : Fin 4) : okW (nthW Th.T i) ∧ wJ (nthW Th.T i) = t3 i := by
  have h := r_all i i.isLt
  unfold rep tOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hc, he⟩, -⟩ := h
  have o := okW_of_chW hc
  exact ⟨o, (eqw o (okW_t3W i) he).trans (wJ_t3W i)⟩

theorem generating_of_ctlA {t g x z₁ h₁ z₂ h₂ : List ℕ} (h : ctlA E t g x z₁ h₁ z₂ h₂ = true)
    (ht : okW t) : ∀ y, IsConj (wJ t) y → SporKRestGenerating 3 y := by
  unfold ctlA at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hg, hx⟩, hz₁⟩, hh₁⟩, hz₂⟩, hh₂⟩, h3⟩, hgt⟩, hl₁⟩, hl₂⟩ := h
  unfold link at hl₁ hl₂
  simp only [Bool.and_eq_true] at hl₁ hl₂
  obtain ⟨⟨e₁, c₁⟩, d₁⟩ := hl₁
  obtain ⟨⟨e₂, c₂⟩, d₂⟩ := hl₂
  have og := okW_of_chW hg
  have ox := okW_of_chW hx
  have oz₁ := okW_of_chW hz₁
  have oh₁ := okW_of_chW hh₁
  have oz₂ := okW_of_chW hz₂
  have oh₂ := okW_of_chW hh₂
  have hX3 : wJ x ^ 3 = 1 := by
    rw [← wJ_repW, ← wJ_nil]
    exact eqw (okW_repW ox 3) okW_nil h3
  have hTX : wJ t * wJ g = wJ g * wJ x := by
    have e := eqw (okW_append og ht) (okW_append ox og) hgt
    rwa [wJ_append, wJ_append] at e
  have hV₁ : wJ ([39] ++ x ++ [39]) = a⁻¹ * wJ x * a := by
    rw [wJ_append, wJ_append, wJ_39, a_inv, mul_assoc]
  have hV₂ : wJ ([40] ++ x ++ [41]) = b⁻¹ * wJ x * b := by
    rw [wJ_append, wJ_append, wJ_40, wJ_41, mul_assoc]
  have path : ∀ {z hh : List ℕ} {c ci : List ℕ}, okW z → okW hh → okW c → okW ci →
      E (hh ++ x) (z ++ hh) = true → cm E x z = true → cm E z (c ++ x ++ ci) = true →
      wJ x * wJ hh = wJ hh * wJ z ∧ wJ x * wJ z = wJ z * wJ x ∧
        wJ z * wJ (c ++ x ++ ci) = wJ (c ++ x ++ ci) * wJ z := by
    intro z hh c ci oz ohh oc oci e cxz czv
    refine ⟨?_, comm_of ox oz cxz, comm_of oz (okW_append (okW_append oc ox) oci) czv⟩
    have e' := eqw (okW_append ohh ox) (okW_append oz ohh) e
    rwa [wJ_append, wJ_append] at e'
  obtain ⟨p₁, q₁, r₁⟩ := path oz₁ oh₁ ok39 ok39 e₁ c₁ d₁
  obtain ⟨p₂, q₂, r₂⟩ := path oz₂ oh₂ ok40 ok41 e₂ c₂ d₂
  rw [hV₁] at r₁
  rw [hV₂] at r₂
  have hgen : SporKRestGenerating 3 (wJ x) :=
    sporKRest_generating_of_paths Nat.prime_three a b closure_ab hX3 ⟨_, _, p₁, q₁, r₁⟩
      ⟨_, _, p₂, q₂, r₂⟩
  intro y hy
  exact hgen.of_isConj ((isConj_of_conj hTX).symm.trans hy)

theorem generating_of_ctlB {t g x : List ℕ} (h : ctlB E t g x = true) (ht : okW t) :
    ∀ y, IsConj (wJ t) y → SporKRestGenerating 3 y := by
  unfold ctlB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hg, hx⟩, h3⟩, hgt⟩, hxb⟩, hxy⟩ := h
  have og := okW_of_chW hg
  have ox := okW_of_chW hx
  have hX3 : wJ x ^ 3 = 1 := by
    rw [← wJ_repW, ← wJ_nil]
    exact eqw (okW_repW ox 3) okW_nil h3
  have hTX : wJ t * wJ g = wJ g * wJ x := by
    have e := eqw (okW_append og ht) (okW_append ox og) hgt
    rwa [wJ_append, wJ_append] at e
  have hb : wJ x * b = b * wJ x := by
    rw [← wJ_40]
    exact comm_of ox ok40 hxb
  have oy : okW ([39] ++ x ++ [39]) := okW_append (okW_append ok39 ox) ok39
  have hy := comm_of ox oy hxy
  have hV : wJ ([39] ++ x ++ [39]) = a * (wJ x * a) := by
    rw [wJ_append, wJ_append, wJ_39]
  have hxh : wJ x * a = a * wJ ([39] ++ x ++ [39]) := by
    rw [hV, ← mul_assoc, ← mul_assoc, a_mul_a, one_mul]
  have hgen : SporKRestGenerating 3 (wJ x) :=
    sporKRest_generating_of_ctrl Nat.prime_three a b closure_ab hX3 hb hy hxh (Or.inr rfl)
  intro y hy'
  exact hgen.of_isConj ((isConj_of_conj hTX).symm.trans hy')

theorem generating_of_cl {t y₁ y₂ g₁ g₂ s o : List ℕ} {M C R : List (List ℕ)} {nR : ℕ}
    (hH : clH E t y₁ y₂ g₁ g₂ s M 16 R nR = true) (hL : ∀ j < 8, clL E y₁ y₂ 4 M j = true)
    (hS : ∀ k < nR, stOK E M C R k = true) (hP : prOK E R o = true) (ht : okW t) (os : okW s)
    (oo : okW o) (hab : Subgroup.closure ({wJ s, wJ o} : Set J) = ⊤) :
    ∀ y, IsConj (wJ t) y → SporKRestGenerating 3 y := by
  unfold clH at hH
  simp only [Bool.and_eq_true] at hH
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hM, hR⟩, hy₁⟩, hy₂⟩, hg₁⟩, hg₂⟩, hMc⟩, hRc⟩, h31⟩, h32⟩, e₁⟩, e₂⟩, hc⟩,
    hs⟩ := hH
  have hMl := (lenLe_iff _ _).1 hM
  have hRl := (lenLe_iff _ _).1 hR
  have o1 := okW_of_chW hy₁
  have o2 := okW_of_chW hy₂
  have og₁ := okW_of_chW hg₁
  have og₂ := okW_of_chW hg₂
  have oM := okW_nthW hMc
  have h1 : wJ y₁ ^ 3 = 1 := by
    rw [← wJ_repW, ← wJ_nil]
    exact eqw (okW_repW o1 3) okW_nil h31
  have h2 : wJ y₂ ^ 3 = 1 := by
    rw [← wJ_repW, ← wJ_nil]
    exact eqw (okW_repW o2 3) okW_nil h32
  have hT₁ : wJ t * wJ g₁ = wJ g₁ * wJ y₁ := by
    have e := eqw (okW_append og₁ ht) (okW_append o1 og₁) e₁
    rwa [wJ_append, wJ_append] at e
  have hT₂ : wJ t * wJ g₂ = wJ g₂ * wJ y₂ := by
    have e := eqw (okW_append og₂ ht) (okW_append o2 og₂) e₂
    rwa [wJ_append, wJ_append] at e
  have hY₁ : wJ y₁ = (wJ g₁)⁻¹ * wJ t * wJ g₁ := by
    rw [mul_assoc, hT₁, ← mul_assoc, inv_mul_cancel, one_mul]
  have hY₂ : wJ y₂ = (wJ g₂)⁻¹ * wJ t * wJ g₂ := by
    rw [mul_assoc, hT₂, ← mul_assoc, inv_mul_cancel, one_mul]
  have hh : wJ y₁ * ((wJ g₁)⁻¹ * wJ g₂) = (wJ g₁)⁻¹ * wJ g₂ * wJ y₂ := by
    rw [hY₁, hY₂]
    group
  have hc' := comm_of o1 o2 hc
  let L : Subgroup J := Subgroup.closure
    ((Subgroup.centralizer {wJ y₁} : Set J) ∪ Subgroup.centralizer {wJ y₂})
  have hlet : ∀ k, wJ (nthW M k) ∈ L := by
    refine wJ_mem_of_nthW hMl fun k hk => ?_
    have hj := hL (k / 2) (by omega)
    unfold clL at hj
    rw [Bool.and_eq_true] at hj
    obtain ⟨hinv, hj⟩ := hj
    have hw : wJ (nthW M (2 * (k / 2))) ∈ L := by
      apply Subgroup.subset_closure
      by_cases h4 : k / 2 < 4
      · have hb : Nat.blt (k / 2) 4 = true := by
          rw [Nat.blt_eq]
          exact h4
        rw [hb, cond_true] at hj
        exact Or.inl (Subgroup.mem_centralizer_singleton_iff.2 (comm_of (oM _) o1 hj))
      · have hb : Nat.blt (k / 2) 4 = false := by
          rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
          exact h4
        rw [hb, cond_false] at hj
        exact Or.inr (Subgroup.mem_centralizer_singleton_iff.2 (comm_of (oM _) o2 hj))
    have hinv' := eqw (okW_append (oM _) (oM _)) okW_nil hinv
    rw [wJ_append, wJ_nil, mul_eq_one_iff_eq_inv] at hinv'
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have e : 2 * j / 2 = j := by omega
      rwa [e] at hw
    · have e : (2 * j + 1) / 2 = j := by omega
      rw [e] at hw hinv'
      rw [hinv']
      exact L.inv_mem hw
  have hstg : ∀ k, wJ (nthW R k) ∈ L := by
    refine wJ_mem_of_nthW hRl fun k hk => ?_
    have h := hS k hk
    unfold stOK at h
    rw [← eqw (okW_expC hMc _) (okW_nthW hRc k) h]
    exact wJ_mem_expC hlet _
  have hsL : wJ s ∈ L :=
    Subgroup.subset_closure (Or.inl (Subgroup.mem_centralizer_singleton_iff.2
      (comm_of o1 os hs).symm))
  have hoL : wJ o ∈ L := by
    unfold prOK at hP
    rw [← eqw (okW_catW hRc) oo hP]
    exact wJ_mem_catW' hstg
  have hgen : L = ⊤ := by
    rw [eq_top_iff, ← hab, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hsL
    · exact hoL
  intro y hy
  exact sporKRest_generating_of_twoCent Nat.prime_three h1 h2 hc' hh hgen
    ((isConj_of_conj hT₁).symm.trans hy)

theorem sporKRestCover_three_J :
    SporKRestCover 3 ↥CFSG.Sporadic.Fi23.J := by
  have hgen : ∀ i : Fin 4, ∀ y, IsConj (t3 i) y → SporKRestGenerating 3 y := by
    intro i
    obtain ⟨ot, et⟩ := rep_facts i
    rw [← et]
    fin_cases i
    · exact generating_of_ctlA Ck.ctl0 ot
    · exact generating_of_ctlB Ck.ctl1 ot
    · refine generating_of_cl Ck.cH cL_all (fun k hk => cS_all k hk) Ck.cP ot ok39 ok40 ?_
      rw [wJ_39, wJ_40]
      exact closure_ab
    · refine generating_of_cl Ck.dH dL_all (fun k hk => dS_all k hk) Ck.dP ot ok40 ok39 ?_
      rw [wJ_39, wJ_40, Set.pair_comm]
      exact closure_ab
  refine sporKRest_cover_of_classes Nat.prime_three (List.ofFn t3) ?_ ?_
  · intro s hs
    obtain ⟨i, hi⟩ := fi23_three_classes s hs
    exact ⟨t3 i, List.mem_ofFn.2 ⟨i, rfl⟩, hi.symm⟩
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hr
    exact hgen i

end CFSG.KD.Fi23Cov

end
