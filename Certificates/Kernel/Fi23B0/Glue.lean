module

public import Certificates.Kernel.Fi23B0.Data
public import Certificates.Kernel.Fi23M.Keys
public import CFSG.Sporadic.Fi23.Simple
public import CFSG.Sporadic.Fi23.Classes
import Certificates.Kernel.Fi23B0.Check
import Certificates.Kernel.Fi23K.Chain
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23B0

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.Raw.Orb CFSG.KD.Fi23K
  CFSG.KD.Fi23B0 CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

theorem lv2_eq : levelLetters (chainLetters orbLit) chainBase 2 = (lvK LL BB 24 2).toArray :=
  levelLetters_eq chain_hyp 2 (by norm_num)

noncomputable abbrev treeB : Tree := tbfsRec 31671 693 (TB 0) (TB 1) (TB 2) (TB 3)

theorem tree_ok : treeOK 31671 28381 treeB (chainLetters orbLit)
    (levelLetters (chainLetters orbLit) chainBase 2) = true := by
  rw [lv2_eq]
  have hh := CFSG.KD.Fi23B0.hd_ok
  unfold hdB hdK at hh
  have hs := CFSG.KD.Fi23B0.pts_ok
  unfold ptsB ptsK at hs
  have hp := fun k (hk : k < 693) => sl_spec hs k (Nat.zero_le k) (by omega) hk
  refine (tbfsK_sound (L := LL) (LV := lvAt LL BB 24 2) (TI := TB 4) ⟨by simp, fun t ht => ?_⟩
    hh hp).2
  have ht' : t < (lvK LL BB 24 2).length := by simpa using ht
  have hm := List.getElem_mem ht'
  have hlt : (lvK LL BB 24 2)[t] < 24 := by
    unfold lvK at hm
    exact List.mem_range.1 (List.mem_filter.1 hm).1
  have e : (lvK LL BB 24 2).toArray[t]! = lvAt LL BB 24 2 t := by
    rw [getElem!_pos _ t (by simpa using ht')]
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e]
  have e2 : lvAt LL BB 24 2 t = (lvK LL BB 24 2)[t] := by
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e2]
  exact ⟨rfl, by rw [letters_TR.1]; exact hlt, fun x hx => ((letters_TR.2 _ hlt).2 x hx).1⟩

theorem treeB_size : treeB.pts.size = 693 := Array.size_ofFn


theorem letters_eq : CFSG.Sporadic.Fi23.letters = chainLetters orbLit := by
  change chainLetters (orbitData ()) = _
  rw [orbitData_eq']

theorem treeFacts_two : TreeFacts 31671 treeB
    (levelLetters CFSG.Sporadic.Fi23.letters chainBase 2) (pairG gs) 28381 :=
  treeOK_facts (fun l hl => rep_pairG_all l (levelLetters_lt hl)) (by rw [letters_eq]; exact tree_ok)

theorem card_orbit_two :
    Nat.card (MulAction.orbit (lvl 2) (⟨28381, by norm_num⟩ : Fin 31671)) = 693 := by
  rw [← treeB_size]
  exact treeFacts_two.card_orbit

theorem idx_letter {l : ℕ} (hl : l < 24) {x : ℕ} (hx : x < 31671) :
    idx 31671 (pairG gs l) x = LL l x := by
  have hsz : CFSG.Sporadic.Fi23.letters.size = 24 := by rw [letters_eq]; exact letters_TR.1
  rw [← rep_pairG_all l (by omega) x hx, letters_eq]
  exact ((letters_TR.2 l hl).2 x hx).1

theorem wvL_lt : ∀ w : List ℤ, (∀ z ∈ w, z.toNat < 24) → ∀ x < 31671, wvL w x < 31671
  | [], _, x, hx => hx
  | z :: w, h, x, hx => LL_lt (h z List.mem_cons_self)
      (wvL_lt w (fun y hy => h y (List.mem_cons_of_mem z hy)) x hx)

theorem idx_word : ∀ w : List ℤ, (∀ z ∈ w, z.toNat < 24) → ∀ x < 31671,
    idx 31671 (wordG jG w) x = wvL w x
  | [], _, x, _ => by simp [wordG, idx_one, wvL]
  | z :: w, h, x, hx => by
    have h' : ∀ y ∈ w, y.toNat < 24 := fun y hy => h y (List.mem_cons_of_mem z hy)
    have e : wordG jG (z :: w) = jG z * wordG jG w := by simp [wordG]
    rw [e, idx_mul, idx_word w h' x hx, jG, idx_letter (h z List.mem_cons_self) (wvL_lt w h' x hx)]
    rfl

theorem ltW_spec {w : List ℤ} (h : ltW w = true) : ∀ z ∈ w, z.toNat < 24 := by
  intro z hz
  unfold ltW at h
  rw [List.all_eq_true] at h
  have := h z hz
  rwa [Nat.blt_eq] at this

theorem inS_spec {p : ℕ} (h : inS p = true) : p = 2776 ∨ p = 14566 ∨ p = 18249 := by
  unfold inS at h
  rw [bIf_eq, bIf_eq] at h
  split_ifs at h with h1 h2
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
  · exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h))

theorem maps3_spec {w : List ℤ} {a b c a' b' c' : ℕ}
    (h : maps3 w a b c a' b' c' = true) : wvL w a = a' ∧ wvL w b = b' ∧ wvL w c = c' := by
  unfold maps3 at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

abbrev InS (p : ℕ) : Prop := p = 2776 ∨ p = 14566 ∨ p = 18249

theorem sylWords_size : (sylWords ()).size = 21 := by decide

theorem sylZ_eq : sylZ = (sylWords ()).toList := by decide +kernel

theorem syl_facts : (∀ j < 21, idx 31671 (sylG j) 2776 = 2776 ∧
      ∀ p, InS p → InS (idx 31671 (sylG j) p)) ∧
    idx 31671 (sylG 1) 14566 = 18249 ∧ idx 31671 (sylG 1) 18249 = 14566 := by
  have h := CFSG.KD.Fi23B0.syl_ok
  unfold sylB sylK at h
  rw [sylZ_eq] at h
  simp only [bAnd_eq, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall, h1⟩ := h
  have hw : ∀ j < 21, ltW (sylWords ())[j]! = true ∧
      Nat.beq (wvL (sylWords ())[j]! 2776) 2776 = true ∧ presS (sylWords ())[j]! = true := by
    intro j hj
    have hj' : j < (sylWords ()).size := by rw [sylWords_size]; exact hj
    have hm : (sylWords ())[j]! ∈ (sylWords ()).toList := by
      rw [getElem!_pos _ j hj', Array.mem_toList_iff]
      exact Array.getElem_mem hj'
    exact hall _ hm
  have e1 : (sylWords ()).toList.getD 1 [] = (sylWords ())[1]! := by
    rw [getElem!_pos _ 1 (by rw [sylWords_size]; norm_num), List.getD_eq_getElem?_getD,
      Array.getElem?_toList, Array.getElem?_eq_getElem (by rw [sylWords_size]; norm_num)]
    rfl
  rw [e1] at h1
  have hsyl : ∀ j < 21, ∀ x < 31671, idx 31671 (sylG j) x = wvL (sylWords ())[j]! x :=
    fun j hj x hx => idx_word _ (ltW_spec (hw j hj).1) x hx
  obtain ⟨-, h1u, h1v⟩ := maps3_spec h1
  refine ⟨fun j hj => ⟨?_, fun p hp => ?_⟩, ?_, ?_⟩
  · rw [hsyl j hj _ (by norm_num)]
    exact Nat.eq_of_beq_eq_true (hw j hj).2.1
  · have hpS := (hw j hj).2.2
    unfold presS at hpS
    simp only [bAnd_eq, Bool.and_eq_true] at hpS
    rcases hp with rfl | rfl | rfl
    · rw [hsyl j hj _ (by norm_num)]; exact inS_spec hpS.1
    · rw [hsyl j hj _ (by norm_num)]; exact inS_spec hpS.2.1
    · rw [hsyl j hj _ (by norm_num)]; exact inS_spec hpS.2.2
  · rw [hsyl 1 (by norm_num) _ (by norm_num)]; exact h1u
  · rw [hsyl 1 (by norm_num) _ (by norm_num)]; exact h1v

theorem mover_facts : idx 31671 (wordG jG moverW) 2776 = 14566 ∧
    idx 31671 (wordG jG moverW) 14566 = 2776 ∧ idx 31671 (wordG jG moverW) 18249 = 18249 := by
  have h := CFSG.KD.Fi23B0.mover_ok
  unfold moverB moverK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  have hw := idx_word _ (ltW_spec h.1)
  obtain ⟨h1, h2, h3⟩ := maps3_spec h.2
  exact ⟨by rw [hw _ (by norm_num)]; exact h1, by rw [hw _ (by norm_num)]; exact h2,
    by rw [hw _ (by norm_num)]; exact h3⟩

theorem conj_facts : idx 31671 (wordG jG gW) 0 = 2776 ∧ idx 31671 (wordG jG gW) 1 = 14566 ∧
    idx 31671 (wordG jG gW) 28381 = 18249 := by
  have h := CFSG.KD.Fi23B0.conj_ok
  unfold conjB conjK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  have hw := idx_word _ (ltW_spec h.1)
  obtain ⟨h1, h2, h3⟩ := maps3_spec h.2
  exact ⟨by rw [hw _ (by norm_num)]; exact h1, by rw [hw _ (by norm_num)]; exact h2,
    by rw [hw _ (by norm_num)]; exact h3⟩

end CertificateChecks.KernelFi23B0

end
