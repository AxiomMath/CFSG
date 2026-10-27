
module

public import Certificates.Kernel.MonsterB.Quad3078.Twin
public import CFSG.Certificates.Kernel.MonsterB.PairBfsSound
public import CFSG.Certificates.Kernel.BabyMonster.OrbTreeWSound

public section

namespace CertificateChecks.KernelMonB.Quad3078

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.Code CFSG.KC.Q3078 CFSG.KD.Q3078
  CFSG.KC.BM.OrbW CFSG.KC.BM.OrbT CFSG.KC.BM CFSG.Monster.B.Sp8.Native

theorem pairImg_eq {k q : ℕ} (hk : k < 45) (hq : q < 65536) :
    pairImg affTab k q = 256 * affN k (q / 256) + affN k (q % 256) := by
  unfold pairImg
  rw [affTab_get' hk (by omega), affTab_get' hk (by omega)]

theorem pairK_eq {k q : ℕ} (hk : k < 45) (hq : q < 65536) : pairK RW CK k q = pairImg affTab k q := by
  rw [pairImg_eq hk hq]
  change 256 * affK RW CK k (q / 256) + affK RW CK k (q % 256) = _
  rw [affK_eq hk, affK_eq hk]

theorem zdK_iff (p : ℕ) :
    zdK ZM p = true ↔ ZM.testBit (p / 256) = true ∧ ZM.testBit (p % 256) = true ∧ p / 256 ≠ p % 256 := by
  have e : zdK ZM p = andB (Nat.beq (bitK ZM (p / 256)) 1)
      (andB (Nat.beq (bitK ZM (p % 256)) 1) (notB (Nat.beq (p / 256) (p % 256)))) := rfl
  have hn : ∀ b : Bool, notB b = true ↔ b = false := by decide
  rw [e, andB_eq_true, andB_eq_true, beq_iff, beq_iff, bitK_eq, bitK_eq, hn, Bool.eq_false_iff,
    Ne, beq_iff]
  cases ZM.testBit (p / 256) <;> cases ZM.testBit (p % 256) <;> simp

@[expose] noncomputable def zSet : Finset ℕ := (Finset.range 256).filter fun a => ZM.testBit a = true

theorem cntK_card : ∀ t, cntK ZM t = ((Finset.range t).filter fun a => ZM.testBit a = true).card := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    change cntK ZM t + bitK ZM t = _
    rw [ih, Finset.range_add_one, Finset.filter_insert, bitK_eq]
    by_cases h : ZM.testBit t = true
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg h, if_neg h, Nat.add_zero]

theorem zSet_card : zSet.card = 120 := by
  rw [zSet, ← cntK_card]
  exact Nat.eq_of_beq_eq_true cnt

@[expose] noncomputable def zdSet : Finset ℕ := (Finset.range 65536).filter fun p => zdK ZM p = true

theorem zdSet_card_le : zdSet.card ≤ 14280 := by
  have hsub : zdSet ⊆ zSet.offDiag.image fun ab => 256 * ab.1 + ab.2 := by
    intro p hp
    simp only [zdSet, Finset.mem_filter, Finset.mem_range, zdK_iff] at hp
    obtain ⟨hp, h1, h2, h3⟩ := hp
    refine Finset.mem_image.2 ⟨(p / 256, p % 256), ?_, by simp; omega⟩
    simp only [Finset.mem_offDiag, zSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, h1⟩, ⟨by omega, h2⟩, h3⟩
  calc zdSet.card ≤ (zSet.offDiag.image fun ab => 256 * ab.1 + ab.2).card := Finset.card_le_card hsub
    _ ≤ zSet.offDiag.card := Finset.card_image_le
    _ = 14280 := by rw [Finset.offDiag_card, zSet_card]

theorem mem_rec {p : ℕ} (hp : p < 65536) (hz : zdK ZM p = true) : ∃ i < 14280, ptB 1020 SB i = p := by
  have hc := ptsB_card inc
  have hsub : ptsB 1020 14280 SB ⊆ zdSet := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_ptsB.1 hx
    simp only [zdSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨hc.2 _ hx, zd i hi⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc.1]; exact zdSet_card_le)
  have : p ∈ ptsB 1020 14280 SB := by
    rw [heq]
    simp only [zdSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨hp, hz⟩
  exact mem_ptsB.1 this

theorem rec_lt {i : ℕ} (hi : i < 14280) : ptB 1020 SB i < 65536 := (incB_spec (inc i hi)).1

theorem rec_visited : ∀ i < 14280, (pairBFS affTab 1).2[ptB 1020 SB i]! ≠ 100000 := by
  have hspec := CFSG.KC.PairBfs.pairBFS_spec (tab := affTab) (root := 1) (by norm_num)
  have hreach : ∀ d, ∀ i < 14280, OrbW.tDep (ptB 1020 TB i) = d →
      (pairBFS affTab 1).2[ptB 1020 SB i]! ≠ 100000 := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      rw [(treeB_spec (tree i hi)).1 hd, Nat.eq_of_beq_eq_true root, hspec.1]
      decide
    | succ d ih =>
      intro i hi hd
      obtain ⟨hp, hl, hdp, he⟩ := (treeB_spec (tree i hi)).2 (by omega)
      have hv := ih _ hp (by omega)
      rw [← he, pairK_eq hl (rec_lt hp)]
      refine hspec.2.2 _ (rec_lt hp) hv _ (by rw [affTab_size']; exact hl) ?_
      rw [← pairK_eq hl (rec_lt hp), he]
      exact rec_lt hi
  exact fun i hi => hreach _ i hi rfl

theorem zeroTab_true {a : ℕ} (ha : a < 256) : zeroTab[a]! = ZM.testBit a := by
  rw [zeroTab_get' ha, zm_ok a ha]

theorem pairCheck_ok : pairCheck affTab zeroTab 1 = true := by
  have hspec := CFSG.KC.PairBfs.pairBFS_spec (tab := affTab) (root := 1) (by norm_num)
  unfold pairCheck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨hspec.1, fun p hp => ?_⟩
  have ha : p / 256 < 256 := by omega
  have hb : p % 256 < 256 := by omega
  split
  · rename_i hc
    simp only [bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    rw [zeroTab_true ha] at h1
    rw [zeroTab_true hb] at h2
    obtain ⟨i, hi, hpi⟩ := mem_rec hp ((zdK_iff p).2 ⟨h1, h2, h3⟩)
    have hv := rec_visited i hi
    rw [hpi] at hv
    obtain ⟨hk, hq, hd, he⟩ := hspec.2.1 p hp hv h4
    generalize (pairBFS affTab 1).1[p]! / 65536 = k at hk hd he
    generalize (pairBFS affTab 1).1[p]! % 65536 = q at hq hd he
    rw [affTab_size'] at hk
    rw [pairImg_eq hk hq] at he
    have hpa : p / 256 = affN k (q / 256) := by
      have := affN_lt hk (q % 256)
      omega
    have hpb : p % 256 = affN k (q % 256) := by
      have := affN_lt hk (q % 256)
      omega
    have hqa : q / 256 < 256 := by omega
    have hqb : q % 256 < 256 := by omega
    have z1 : zeroTab[q / 256]! = true := by
      rw [zeroTab_get' hqa, ← qN_affN' hk hqa, ← hpa, ← zeroTab_get' ha, zeroTab_true ha, h1]
    have z2 : zeroTab[q % 256]! = true := by
      rw [zeroTab_get' hqb, ← qN_affN' hk hqb, ← hpb, ← zeroTab_get' hb, zeroTab_true hb, h2]
    have hne : q / 256 ≠ q % 256 := fun e => h3 (by rw [hpa, hpb, e])
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, affTab_size']
    refine ⟨⟨⟨⟨⟨hk, hd⟩, ?_⟩, z1⟩, z2⟩, hne⟩
    rw [pairImg_eq hk hq]
    omega
  · rfl

end CertificateChecks.KernelMonB.Quad3078

end
