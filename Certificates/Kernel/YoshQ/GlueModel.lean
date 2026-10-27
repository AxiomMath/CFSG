module

public import Certificates.Kernel.YoshQ.GlueRec
public import Certificates.Kernel.YoshQ.NC

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.EvenSporadicStandard.Fin76b
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem normCenEnumCheck_true {m size sizeE : Nat} {g gE : Array Table}
    {L LE : Array Table × Array Nat × Array Nat} {cT : Table} {G GE RL REL : List Nat} {c : Nat}
    (hg : g = (G.map (tabN 16 5)).toArray) (hgE : gE = (GE.map (tabN 16 5)).toArray)
    (hL : L.1 = (RL.map (tabN 16 5)).toArray) (hLE : LE.1 = (REL.map (tabN 16 5)).toArray)
    (hc : cT = tabN 16 5 c)
    (h1 : enumOK 16 m g L size = true) (h2 : enumOK 16 m gE LE sizeE = true)
    (h3 : CFSG.Sporadic.SmallOddCore.permOK 16 cT = true)
    (h4 : normCenRestN 16 5 G GE RL REL c = true) :
    normCenEnumCheck 16 m g gE L LE size sizeE cT = true := by
  unfold normCenEnumCheck
  rw [h1, h2, h3]
  simp only [Bool.true_and]
  subst hg hgE hc
  rw [hL, hLE]
  unfold normCenRestN at h4
  simpa only [List.any_toArray, List.all_toArray, all_map_tabN, any_map_tabN, tblEq_tabN' dims16,
    compT_tabN' dims16, commTT_tabN dims16, idT_tabN' dims16, Bool.and_assoc] using h4

theorem modelT_c {GS : List Nat} {k : Nat} [NeZero k] {g : Array Table}
    (hg : g = (GS.map (tabN 16 5)).toArray) (hk : k ≤ GS.length) :
    modelT 16 k g [(0, true), (0, true)] = tabN 16 5 (modelTN 16 5 k GS [(0, true), (0, true)]) := by
  rw [hg]
  exact modelT_tabN dims16 hk _

theorem eModelCheck_true : eModelCheck = true := by
  unfold eModelCheck normCenCheck
  have he := eg_ok.enumOK (size := 128) (by decide) (by decide) (by decide) (Nat.le_refl _)
    (gensOK_spec g_eg.1).2 (by decide)
  have hc : eCT = tabN 16 5 (modelTN 16 5 6 EG.GS [(0, true), (0, true)]) :=
    modelT_c eg_ok.gens_eq (by decide)
  have hL := eg_ok.closure_fst (by decide) (by decide) (by decide) (Nat.le_refl _)
  exact normCenEnumCheck_true eg_ok.gens_eq eg_ok.gens_eq hL hL hc he he nc_e.2 nc_e.1

theorem nModelCheck_of {α k : Nat} {GS RL GES REL : List Nat} {cnt EP PL POS cntE EPE PLE POSE : Nat}
    {SM SF SME SFE : List Nat}
    (R : RecOK 16 5 16 4000 (nGens α k) GS RL cnt EP PL POS SM SF)
    (RE : RecOK 16 5 16 4000 (nEGens α k) GES REL cntE EPE PLE POSE SME SFE)
    (hp : gensOK 16 5 (nGens α k) GS = true) (hpE : gensOK 16 5 (nEGens α k) GES = true)
    (hl : 9 ≤ GS.length) (hc : cnt = 3072) (hcE : cntE = 128)
    (h : normCenRestN 16 5 GS GES RL REL (modelTN 16 5 9 GS [(0, true), (0, true)]) = true ∧
      CFSG.Sporadic.SmallOddCore.permOK 16 (nCT α k) = true) :
    nModelCheck α k = true := by
  unfold nModelCheck normCenCheck
  have he := R.enumOK (size := 3072) (by decide) (by decide) (by decide) (Nat.le_refl _)
    (gensOK_spec hp).2 hc
  have heE := RE.enumOK (size := 128) (by decide) (by decide) (by decide) (Nat.le_refl _)
    (gensOK_spec hpE).2 hcE
  have hct : nCT α k = tabN 16 5 (modelTN 16 5 9 GS [(0, true), (0, true)]) :=
    modelT_c R.gens_eq hl
  exact normCenEnumCheck_true R.gens_eq RE.gens_eq
    (R.closure_fst (by decide) (by decide) (by decide) (Nat.le_refl _))
    (RE.closure_fst (by decide) (by decide) (by decide) (Nat.le_refl _)) hct he heE h.2 h.1

theorem lemma5ModelCheck_true : lemma5ModelCheck = true := by
  have h00 := nModelCheck_of n00_ok ne00_ok g_n00.1 g_ne.1 (by decide) (by decide) (by decide) nc_00
  have h01 := nModelCheck_of n01_ok ne01_ok g_n01.1 g_ne.2.1 (by decide) (by decide) (by decide)
    nc_01
  have h10 := nModelCheck_of n10_ok ne10_ok g_n10.1 g_ne.2.2.1 (by decide) (by decide) (by decide)
    nc_10
  have h11 := nModelCheck_of n11_ok ne11_ok g_n11.1 g_ne.2.2.2 (by decide) (by decide) (by decide)
    nc_11
  simp only [lemma5ModelCheck, List.all_cons, List.all_nil, eModelCheck_true, h00, h01, h10, h11,
    Bool.and_self]

end CertificateChecks.KernelYoshQ

end
