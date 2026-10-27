module

public import Certificates.Kernel.YoshQ.GlueRec
public import Certificates.Kernel.YoshQ.Words5
public import Certificates.Kernel.YoshQ.Fus
public import Certificates.Kernel.YoshQ.UE
public import Certificates.Kernel.YoshQ.L6
public import Certificates.Kernel.YoshQ.L7
public import Certificates.Kernel.YoshQ.L8

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.EvenSporadicStandard.Fin76b
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem tenum_of {gens : Array Table} {GS RL : List Nat} {cnt EP PL POS : Nat} {SM SF : List Nat}
    (R : RecOK 16 5 16 4000 gens GS RL cnt EP PL POS SM SF) :
    tenum gens = (RL.map (tabN 16 5)).toArray :=
  R.closure_fst (by decide) (by decide) (by decide) (Nat.le_refl _)

theorem tsubOK_of {gens : Array Table} {GS RL : List Nat} {cnt EP PL POS : Nat} {SM SF : List Nat}
    {size : Nat} (R : RecOK 16 5 16 4000 gens GS RL cnt EP PL POS SM SF)
    (hp : gens.all (fun x => CFSG.Sporadic.SmallOddCore.permOK 16 x) = true) (hc : cnt = size) :
    tsubOK gens size = true :=
  R.enumOK (by decide) (by decide) (by decide) (Nat.le_refl _) hp hc

theorem fusionChains_true : fusionChainsCheck 0 0 = true ∧ fusionChainsCheck 0 1 = true ∧
    fusionChainsCheck 1 0 = true ∧ fusionChainsCheck 1 1 = true := by
  rw [n00_data.fusionChainsCheck_eq, n01_data.fusionChainsCheck_eq, n10_data.fusionChainsCheck_eq,
    n11_data.fusionChainsCheck_eq]
  exact f_chains

theorem fusionCover_true : fusionCoverCheck 0 0 = true ∧ fusionCoverCheck 0 1 = true ∧
    fusionCoverCheck 1 0 = true ∧ fusionCoverCheck 1 1 = true := by
  rw [n00_data.fusionCoverCheck_eq, n01_data.fusionCoverCheck_eq, n10_data.fusionCoverCheck_eq,
    n11_data.fusionCoverCheck_eq]
  exact ⟨fusionCoverN_of_I n00_rec.2.2 (distinct_of n00_rec.1) (by decide) f_cover00,
    fusionCoverN_of_I n01_rec.2.2 (distinct_of n01_rec.1) (by decide) f_cover01,
    f_cover10, f_cover11⟩

theorem fusionCheck_true : fusionCheck = true := by
  simp only [fusionCheck, List.all_cons, List.all_nil, w_sigma0, w_sigma1, fusionChains_true,
    fusionCover_true, Bool.and_self]

theorem ueCheck_of {α k : Nat} {GN NL GE RE GS RS : List Nat} {cE EPE PLE POSE cS EPS PLS POSS : Nat}
    {SME SFE SMS SFS : List Nat} (h : NData α k GN NL)
    (hE : RecOK 16 5 16 4000 (wgens α k eWords) GE RE cE EPE PLE POSE SME SFE)
    (hS : RecOK 16 5 16 4000 (wgens α k sWords) GS RS cS EPS PLS POSS SMS SFS)
    (hpE : gensOK 16 5 (wgens α k eWords) GE = true) (hpS : gensOK 16 5 (wgens α k sWords) GS = true)
    (hcE : cE = 128) (hcS : cS = 1024)
    (hue : ueN GE GS (nTN GN (swN cWord)) RE RS = true)
    (hes : esN GE GS (nTN GN (swN cWord)) RE RS GN = true) :
    ueCheck α k = true ∧ esCheck α k = true := by
  have t1 := tsubOK_of hE (gensOK_spec hpE).2 hcE
  have t2 := tsubOK_of hS (gensOK_spec hpS).2 hcS
  constructor
  · unfold ueCheck ueCheckG
    rw [t1, t2, tenum_of hE, tenum_of hS, hE.gens_eq, hS.gens_eq, h.nwT_eq, ueEnumCheck_eq]
    exact hue
  · unfold esCheck
    rw [tenum_of hE, tenum_of hS, hE.gens_eq, hS.gens_eq, h.nwT_eq, h.gens, esEnumCheck_eq]
    exact hes

theorem ueEs_true : (ueCheck 0 0 = true ∧ esCheck 0 0 = true) ∧
    (ueCheck 0 1 = true ∧ esCheck 0 1 = true) ∧ (ueCheck 1 0 = true ∧ esCheck 1 0 = true) ∧
    (ueCheck 1 1 = true ∧ esCheck 1 1 = true) :=
  ⟨ueCheck_of n00_data e00_ok s00_ok g_e.1 g_s.1 (by decide) (by decide) ue00 es_all.1,
    ueCheck_of n01_data e01_ok s01_ok g_e.2.1 g_s.2.1 (by decide) (by decide) ue01 es_all.2.1,
    ueCheck_of n10_data e10_ok s10_ok g_e.2.2.1 g_s.2.2.1 (by decide) (by decide) ue10
      es_all.2.2.1,
    ueCheck_of n11_data e11_ok s11_ok g_e.2.2.2 g_s.2.2.2 (by decide) (by decide) ue11
      es_all.2.2.2⟩

theorem l6Check_of {k : Nat} {GN NL GE RE : List Nat} {cE EPE PLE POSE : Nat} {SME SFE : List Nat}
    (h : NData 0 k GN NL)
    (hE : RecOK 16 5 16 4000 (wgens 0 k eWords) GE RE cE EPE PLE POSE SME SFE)
    (hl : l6N NL (goodTabsN GN NL 0 k) (nTN GN (swN eWord)) RE = true) : l6Check 0 k = true := by
  unfold l6Check
  rw [h.enum, h.goodTabs_eq, h.nwT_eq, tenum_of hE, toList_map_tabN, l6Core_eq]
  exact hl

theorem l6_true : l6Check 0 0 = true ∧ l6Check 0 1 = true :=
  ⟨l6Check_of n00_data e00_ok l6_0, l6Check_of n01_data e01_ok l6_1⟩

theorem l7Check_of {k : Nat} {GN NL GE RE GS RS GA RA GG RG : List Nat}
    {cE EPE PLE POSE cS EPS PLS POSS cA EPA PLA POSA cG EPG PLG POSG : Nat}
    {SME SFE SMS SFS SMA SFA SMG SFG : List Nat}
    (h : NData 1 k GN NL)
    (hE : RecOK 16 5 16 4000 (wgens 1 k eWords) GE RE cE EPE PLE POSE SME SFE)
    (hS : RecOK 16 5 16 4000 (wgens 1 k sWords) GS RS cS EPS PLS POSS SMS SFS)
    (hA : RecOK 16 5 16 4000 (wgens 1 k aWords) GA RA cA EPA PLA POSA SMA SFA)
    (hG : RecOK 16 5 16 4000 ((GG.map (tabN 16 5)).toArray) GG RG cG EPG PLG POSG SMG SFG)
    (hpA : gensOK 16 5 (wgens 1 k aWords) GA = true)
    (hpG : ((GG.map (tabN 16 5)).toArray).all
      (fun x => CFSG.Sporadic.SmallOddCore.permOK 16 x) = true)
    (hcA : cA = 16) (hcG : cG = 128)
    (hgE : RE.filter (memN 16 5 (goodTabsN GN NL 1 k)) = GG)
    (hf : l7FusionN NL (goodTabsN GN NL 1 k) (nTN GN (swN eWord)) (nTN GN (swN uWord)) RE = true)
    (hs : l7SylowN (nTN GN (swN cWord)) (nTN GN (swN eWord)) (nTN GN (swN uWord)) RE RS = true)
    (ha : l7AN (badTabsN GN NL 1 k) (nTN GN (swN cWord)) GA RA RE RS = true)
    (hv : l7VN NL (vWords.map fun W => nTN GN (swN W)) = true)
    (hb : ((badChains 1 k).all fun c => c.1 == [1, 1]) = true) : l7Check 1 k = true := by
  have htf : tsubOK (((RE.filter (memN 16 5 (goodTabsN GN NL 1 k))).map (tabN 16 5)).toArray) 128 =
      true := by
    rw [hgE]
    exact tsubOK_of hG hpG hcG
  have hAe : tenum ((GA.map (tabN 16 5)).toArray) = (RA.map (tabN 16 5)).toArray := by
    rw [← hA.gens_eq]
    exact tenum_of hA
  have htA : tsubOK ((GA.map (tabN 16 5)).toArray) 16 = true := by
    rw [← hA.gens_eq]
    exact tsubOK_of hA (gensOK_spec hpA).2 hcA
  unfold l7Check
  simp only []
  rw [tenum_of hE, tenum_of hS, h.enum, h.goodTabs_eq, h.badTabs_eq, toList_map_tabN,
    toList_map_tabN, h.nwT_eq, h.nwT_eq, h.nwT_eq, hA.gens_eq, h.wgens_eq vWords,
    l7Fusion_eq _ _ _ _ _ htf, l7Sylow_eq, l7A_eq _ _ _ _ _ _ hAe htA, l7V_eq, hf, hs, ha, hv, hb]
  rfl

theorem l8Check_of {k : Nat} {GN NL GE RE : List Nat} {cE EPE PLE POSE : Nat} {SME SFE : List Nat}
    (h : NData 1 k GN NL)
    (hE : RecOK 16 5 16 4000 (wgens 1 k eWords) GE RE cE EPE PLE POSE SME SFE)
    (hf : l8FactN NL (nTN GN (swN eWord)) = true)
    (hz : l8ZNN NL (nTN GN (swN cWord)) (nTN GN (jIn 1 (swN [7, 8]))) RE = true)
    (hc : l8Chain 1 k (RE.map (tabN 16 5)) = true) : l8Check 1 k = true := by
  unfold l8Check
  simp only []
  have hj : jTab 1 k [7, 8] = tabN 16 5 (nTN GN (jIn 1 (swN [7, 8]))) := h.nT_eq _
  rw [tenum_of hE, toList_map_tabN, h.enum, h.nwT_eq, h.nwT_eq, hj, l8Fact_eq, l8ZN_eq, hf, hz, hc]
  rfl

theorem l78_true : (l7Check 1 0 = true ∧ l8Check 1 0 = true) ∧
    (l7Check 1 1 = true ∧ l8Check 1 1 = true) :=
  ⟨⟨l7Check_of n10_data e10_ok s10_ok a10_ok ge10_ok
      g_a.1 g_ge.1 (by decide) (by decide) l7ge.1 l7f_0 l7s.1 l7a_0 l7v.1 l7v.2.2.1,
    l8Check_of n10_data e10_ok l8f.1 l8f.2.2.1 l8c.1⟩,
   ⟨l7Check_of n11_data e11_ok s11_ok a11_ok ge11_ok
      g_a.2 g_ge.2 (by decide) (by decide) l7ge.2 l7f_1 l7s.2 l7a_1 l7v.2.1 l7v.2.2.2,
    l8Check_of n11_data e11_ok l8f.2.1 l8f.2.2.2 l8c.2⟩⟩

theorem sylowHomCheck_of {k : Nat} {GS RL : List Nat} {cnt EP PL POS : Nat} {SM SF : List Nat}
    (R : RecOK 28 5 16 4000 (glueGens (wgens 1 k sWords) (sylowHomData k)) GS RL cnt EP PL POS SM SF)
    (hp : gensOK 28 5 (glueGens (wgens 1 k sWords) (sylowHomData k)) GS = true) (hc : cnt = 1024)
    (h1 : ((wgens 1 k sWords).size == (sylowHomData k).size && (sylowHomData k).all (fun T =>
      CFSG.Sporadic.SmallOddCore.permOK 12 T && evenTab T) &&
      !tblEq 16 (nwT 1 k cWord) (idT 16)) = true)
    (h2 : sylowHomOn ((RL.map (tabN 28 5)).toArray) (nwT 1 k cWord) = true) :
    sylowHomCheck (wgens 1 k sWords) (nwT 1 k cWord) (sylowHomData k) = true := by
  have he := R.enumOK (size := 1024) (by decide) (by decide) (by decide) (by decide)
    (gensOK_spec hp).2 hc
  have hL := R.closure_fst (by decide) (by decide) (by decide) (by decide)
  unfold sylowHomOn at h2
  unfold sylowHomCheck
  simp only []
  rw [hL]
  simp only [Bool.and_eq_true] at h1 h2 he ⊢
  exact ⟨⟨⟨h1, he⟩, h2.1⟩, h2.2⟩

theorem sylowHomCheckAll_true : sylowHomCheckAll = true := by
  simp only [sylowHomCheckAll, List.all_cons, List.all_nil,
    sylowHomCheck_of gl0_ok g_gl.1 (by decide) syl.1 syl.2.2.1,
    sylowHomCheck_of gl1_ok g_gl.2 (by decide) syl.2.1 syl.2.2.2, Bool.and_self]

theorem modelFactsCheck_true : modelFactsCheck = true := by
  simp only [modelFactsCheck, List.all_cons, List.all_nil, fusionCheck_true, ueEs_true, l6_true,
    l78_true, sylowHomCheckAll_true, Bool.and_self]

end CertificateChecks.KernelYoshQ

end
