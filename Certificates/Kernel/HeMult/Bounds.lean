module

public import Certificates.Kernel.HeMult.Tables

public section

namespace CertificateChecks.KernelHeMult

open CFSG.Certificates CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.HeMultiplier

theorem card_le_of_tables3 (ws : List (List (Fin 4 × Bool)))
    {inv L eps nLab nT N₃ RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    {rels words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    {inv' L' eps' nLab' nT' N₂ RW' RM' nR' nS' nW' nF' : ℕ} {F' D' Wd' Wd2' R' S' : ℕ → ℕ}
    {amap' : ℕ} {rels' words' : List (List (ℕ × Bool))} {walk' cov' : List ℕ}
    {inv'' L'' eps'' nLab'' nT'' N₁ RW'' RM'' nR'' nS'' nW'' nF'' : ℕ}
    {F'' D'' Wd'' Wd2'' R'' S'' : ℕ → ℕ} {amap'' : ℕ} {rels'' words'' : List (List (ℕ × Bool))}
    {walk'' cov'' : List ℕ}
    (h3 : KB.tableOk inv L eps nLab nT N₃ RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk
      cov = true) (hr3 : ws.map encW = rels) (ht3 : KB.topOk amap 4 = true)
    (hw3 : words = (subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)])
    (h2 : KB.tableOk inv' L' eps' nLab' nT' N₂ RW' RM' nR' nS' nW' nF' F' D' Wd' Wd2' R' S' amap'
      rels' words' walk' cov' = true)
    (hr2 : (restrictWords (subsetOf 4 [0, 1, 2]) ws).map encW = rels')
    (ht2 : KB.topOk amap' 3 = true)
    (hw2 : words' = (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]).map fun x => [(x.val, true)])
    (h1 : KB.tableOk inv'' L'' eps'' nLab'' nT'' N₁ RW'' RM'' nR'' nS'' nW'' nF'' F'' D'' Wd''
      Wd2'' R'' S'' amap'' rels'' words'' walk'' cov'' = true)
    (hr1 : (restrictWords (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1])
      (restrictWords (subsetOf 4 [0, 1, 2]) ws)).map encW = rels'')
    (ht1 : KB.topOk amap'' 2 = true) (hw1 : words'' = []) :
    Finite (PG 4 ws) ∧ Nat.card (PG 4 ws) ≤ N₃ * (N₂ * N₁) := by
  obtain ⟨f1, c1⟩ := card_le_of_tableOk (restrictWords (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1])
    (restrictWords (subsetOf 4 [0, 1, 2]) ws)) hr1 h1 (by decide) ht1 hw1
  obtain ⟨hfi2, hidx2⟩ := genSub_index_le_of_tableOk (restrictWords (subsetOf 4 [0, 1, 2]) ws) hr2
    h2 (by decide) ht2 (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]) hw2
  obtain ⟨f2, c2⟩ := card_le_of_genSub_index (restrictWords (subsetOf 4 [0, 1, 2]) ws)
    (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]) hfi2 hidx2
  obtain ⟨hfi3, hidx3⟩ := genSub_index_le_of_tableOk ws hr3 h3 (by decide) ht3
    (subsetOf 4 [0, 1, 2]) hw3
  obtain ⟨f3, c3⟩ := card_le_of_genSub_index ws (subsetOf 4 [0, 1, 2]) hfi3 hidx3
  exact ⟨f3, c3.trans (Nat.mul_le_mul_left _ (c2.trans (Nat.mul_le_mul_left _ c1)))⟩

theorem words3_eq : CFSG.KBRoute.HeMP3.T1.words =
    (subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)] := by decide +kernel

theorem words2_eq : CFSG.KBRoute.HeMP2.T1.words =
    (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]).map fun x => [(x.val, true)] := by decide +kernel

theorem wordsC3_eq : CFSG.KBRoute.HeMC3.T1.words =
    (subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)] := by decide +kernel

theorem wordsC2_eq : CFSG.KBRoute.HeMC2.T1.words =
    (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]).map fun x => [(x.val, true)] := by decide +kernel

theorem card_presented : Finite (PG 4 heRels) ∧ Nat.card (PG 4 heRels) ≤ 4030387200 := by
  have h3 := p3
  unfold CFSG.KBRoute.HeMP3.T1.ok at h3
  have h2 := p2
  unfold CFSG.KBRoute.HeMP2.T1.ok at h2
  have h1 := p1
  unfold CFSG.KBRoute.HeMP1.T1.ok at h1
  obtain ⟨f, c⟩ := card_le_of_tables3 heRels h3 rfl CFSG.KBRoute.HeMP3.top words3_eq h2 rfl
    CFSG.KBRoute.HeMP2.top words2_eq h1 rfl CFSG.KBRoute.HeMP1.top rfl
  exact ⟨f, c.trans (by norm_num)⟩

theorem card_cover : Finite (PG 4 heCover) ∧ Nat.card (PG 4 heCover) ≤ 4030387200 := by
  have h3 := c3
  unfold CFSG.KBRoute.HeMC3.T1.ok at h3
  have h2 := c2
  unfold CFSG.KBRoute.HeMC2.T1.ok at h2
  have h1 := c1
  unfold CFSG.KBRoute.HeMC1.T1.ok at h1
  obtain ⟨f, c⟩ := card_le_of_tables3 heCover h3 rfl CFSG.KBRoute.HeMC3.top wordsC3_eq h2 rfl
    CFSG.KBRoute.HeMC2.top wordsC2_eq h1 rfl CFSG.KBRoute.HeMC1.top rfl
  exact ⟨f, c.trans (by norm_num)⟩

end CertificateChecks.KernelHeMult

end
