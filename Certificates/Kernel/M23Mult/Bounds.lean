module

public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Spor.RelSound
public import Certificates.Kernel.M23Mult.Tables
public import Certificates.Kernel.M23Mult.TabK

public section

namespace CertificateChecks.KernelM23Mult

open CFSG.Certificates CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.M23Multiplier
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe

theorem tab : m23TabCheck = true := CFSG.KS.Rel.relK_sound tabK

theorem rels6_eq : m23Rels.map encW = rels6 := by decide +kernel

theorem rels5_eq : m23Rels5.map encW = rels5 := by decide +kernel

theorem cover6_eq : m23Cover.map encW = cover6 := by decide +kernel

theorem cover5_eq : m23Cover5.map encW = cover5 := by decide +kernel

theorem words_eq : CFSG.KBRoute.M23MP2.T1.words =
    (subsetOf 6 [0, 1, 2, 3, 4]).map fun x => [(x.val, true)] := by decide +kernel

theorem wordsC_eq : CFSG.KBRoute.M23MC2.T1.words =
    (subsetOf 6 [0, 1, 2, 3, 4]).map fun x => [(x.val, true)] := by decide +kernel

theorem card_le_of_tables (ws : List (List (Fin 6 × Bool)))
    {inv L eps nLab nT N₂ RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    {rels words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    {inv' L' eps' nLab' nT' N₁ RW' RM' nR' nS' nW' nF' : ℕ} {F' D' Wd' Wd2' R' S' : ℕ → ℕ}
    {amap' : ℕ} {rels' words' : List (List (ℕ × Bool))} {walk' cov' : List ℕ}
    (h2 : KB.tableOk inv L eps nLab nT N₂ RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk
      cov = true) (hr2 : ws.map encW = rels) (ht2 : KB.topOk amap 6 = true)
    (hw2 : words = (subsetOf 6 [0, 1, 2, 3, 4]).map fun x => [(x.val, true)])
    (h1 : KB.tableOk inv' L' eps' nLab' nT' N₁ RW' RM' nR' nS' nW' nF' F' D' Wd' Wd2' R' S' amap'
      rels' words' walk' cov' = true)
    (hr1 : (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) ws).map encW = rels')
    (ht1 : KB.topOk amap' 5 = true) (hw1 : words' = []) :
    Finite (PG 6 ws) ∧ Nat.card (PG 6 ws) ≤ N₂ * N₁ := by
  obtain ⟨f1, c1⟩ := card_le_of_tableOk (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) ws) hr1 h1
    (by decide) ht1 hw1
  obtain ⟨hfi, hidx⟩ := genSub_index_le_of_tableOk ws hr2 h2 (by decide) ht2 _ hw2
  obtain ⟨f0, c0⟩ := card_le_of_genSub_index ws (subsetOf 6 [0, 1, 2, 3, 4]) hfi hidx
  exact ⟨f0, c0.trans (Nat.mul_le_mul_left N₂ c1)⟩

theorem card_presented : Finite (PG 6 m23Rels) ∧ Nat.card (PG 6 m23Rels) ≤ 10200960 := by
  have h2 := p2
  unfold CFSG.KBRoute.M23MP2.T1.ok at h2
  have h1 := p1
  unfold CFSG.KBRoute.M23MP1.T1.ok at h1
  obtain ⟨f, c⟩ := card_le_of_tables m23Rels h2 rels6_eq CFSG.KBRoute.M23MP2.top words_eq h1
    rels5_eq CFSG.KBRoute.M23MP1.top rfl
  exact ⟨f, c.trans (by norm_num)⟩

theorem card_cover : Finite M23Cover ∧ Nat.card M23Cover ≤ 10200960 := by
  change Finite (PresentedGroup (coverRelators (wordSet m23Rels)
      fun i => FreeGroup.mk (m23CommWord i))) ∧
    Nat.card (PresentedGroup (coverRelators (wordSet m23Rels)
      fun i => FreeGroup.mk (m23CommWord i))) ≤ 10200960
  rw [coverRelators_wordSet]
  have h2 := c2
  unfold CFSG.KBRoute.M23MC2.T1.ok at h2
  have h1 := c1
  unfold CFSG.KBRoute.M23MC1.T1.ok at h1
  obtain ⟨f, c⟩ := card_le_of_tables m23Cover h2 cover6_eq CFSG.KBRoute.M23MC2.top wordsC_eq h1
    cover5_eq CFSG.KBRoute.M23MC1.top rfl
  exact ⟨f, c.trans (by norm_num)⟩

end CertificateChecks.KernelM23Mult

end
