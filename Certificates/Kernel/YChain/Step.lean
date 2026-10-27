module

public import CFSG.YGroups.Bound
public import CFSG.Certificates.Kernel.CosetBounds

public section

namespace CertificateChecks.KernelYChain

open CFSG.YGroups CFSG.Certificates CFSG.Certificates.KB CFSG.Certificates.CosetEnumeration

@[expose] def enc (w : List ℕ) : List (ℕ × Bool) := w.map fun c => (c, true)

variable {p q r p' q' r' : ℕ}

theorem sword_enc {G : Type*} [Group G] (gen : ℕ → G) (w : List ℕ) :
    sword gen (enc w) = evalWord gen w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [evalWord_cons, ← ih]
    simp [enc, sword]

theorem sword_rels_y {rels : List (List (ℕ × Bool))} (hrels : rels = (yRels p q r).map enc) :
    ∀ w ∈ rels, sword (yGen p q r) w = 1 := by
  rw [hrels]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  rw [sword_enc]
  exact evalWord_yGen_of_mem hv

theorem alphaSub_y {amap : ℕ} (hn : ngen p q r < 256) (htop : topOk amap (ngen p q r) = true) :
    alphaSub (yGen p q r) amap = ⊤ := by
  rw [alphaSub, ← closure_yGen p q r]
  congr 2
  ext g
  exact topOk_sound hn htop g

theorem index_le_of_table {rels words : List (List (ℕ × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    {walk cov : List ℕ}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hrels : rels = (yRels p q r).map enc) (hn : ngen p q r < 256)
    (htop : topOk amap (ngen p q r) = true) :
    (wordSub (yGen p q r) words).FiniteIndex ∧ (wordSub (yGen p q r) words).index ≤ N := by
  obtain ⟨-, h0, hN⟩ := tableOk_sound (yGen p q r) (sword_rels_y hrels) h
  rw [alphaSub_y hn htop, Subgroup.relIndex_top_right] at h0 hN
  exact ⟨⟨h0⟩, hN⟩

theorem wordSub_letters (m : ℕ → ℕ) (n : ℕ) :
    wordSub (yGen p' q' r') (((List.range n).map m).map fun c => [(c, true)]) =
      Subgroup.closure (yGen p' q' r' '' (m '' Set.Iio n)) := by
  rw [wordSub]
  congr 1
  ext x
  simp only [List.map_map, Set.mem_image, Set.mem_ofPred_eq, List.mem_map, List.mem_range,
    Function.comp_apply, Set.mem_Iio]
  constructor
  · rintro ⟨w, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨m c, ⟨c, hc, rfl⟩, by simp [sword]⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, by simp [sword]⟩

theorem card_le_of_table (m : ℕ → ℕ) (hm : ∀ w ∈ yRels p q r, w.map m ∈ yRels p' q' r')
    {rels words : List (List (ℕ × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    {walk cov : List ℕ}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hrels : rels = (yRels p' q' r').map enc)
    (hwords : words = ((List.range (ngen p q r)).map m).map fun c => [(c, true)])
    (hn : ngen p' q' r' < 256) (htop : topOk amap (ngen p' q' r') = true)
    [Finite (YGroup p q r)] :
    Finite (YGroup p' q' r') ∧ Nat.card (YGroup p' q' r') ≤ N * Nat.card (YGroup p q r) := by
  apply finite_card_le_of_index (yHom m hm)
  rw [range_yHom, ← wordSub_letters, ← hwords]
  exact index_le_of_table h hrels hn htop

theorem card_le_of_table_bot {rels : List (List (ℕ × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    {walk cov : List ℕ}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels [] walk cov =
      true) (hrels : rels = (yRels p q r).map enc) (hn : ngen p q r < 256)
    (htop : topOk amap (ngen p q r) = true) :
    Finite (YGroup p q r) ∧ Nat.card (YGroup p q r) ≤ N := by
  have key := index_le_of_table h hrels hn htop
  have hbot : wordSub (yGen p q r) [] = ⊥ := by simp [wordSub]
  rw [hbot] at key
  have hfi := key.1.index_ne_zero
  rw [Subgroup.index_bot] at hfi
  exact ⟨Nat.finite_of_card_ne_zero hfi, by simpa [Subgroup.index_bot] using key.2⟩

end CertificateChecks.KernelYChain

end
