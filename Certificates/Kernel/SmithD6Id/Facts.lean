module

public import Certificates.Kernel.SmithD6Id.Checks
public import Certificates.Kernel.SmithD6Trees.Facts
public import CFSG.Certificates.Kernel.SmithD6IdSound

set_option maxRecDepth 100000

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.SmithD6Id

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem foldl_range_congr {f g : ℕ → ℕ → ℕ} :
    ∀ {n : ℕ}, (∀ acc, ∀ t < n, f acc t = g acc t) → ∀ a,
      (List.range n).foldl f a = (List.range n).foldl g a := by
  intro n
  induction n with
  | zero => intro _ a; rfl
  | succ n ih =>
    intro h a
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih (fun acc t ht => h acc t (by omega)) a, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      List.foldl_nil, h _ n (by omega)]

theorem getElem!_toArray_map {f : ℕ × ℕ × ℕ → ℕ} {L : List (ℕ × ℕ × ℕ)} {t : ℕ}
    (ht : t < L.length) : (L.map f).toArray[t]! = f L[t] := by
  rw [getElem!_pos _ t (by simpa using ht)]
  simp

theorem getElem!_array_map {f : ℕ × ℕ × ℕ → ℕ} {A : Array (ℕ × ℕ × ℕ)} {t : ℕ}
    (ht : t < A.toList.length) : (A.map f)[t]! = f A.toList[t] := by
  rw [getElem!_pos _ t (by simpa using ht)]
  simp

theorem wt0_pinned : ∃ h : 0 < J.wtC.flatten.length, J.wtC.flatten[0] = 1 := by
  have hH := id7QaHeadK_ok
  simp only [id7QaHeadK, id7QaHeadG, Bool.and_eq_true] at hH
  have h1 := Nat.eq_of_beq_eq_true hH.1.2
  exact SmithD6Trees.wt_facts.2.2.2 1 0 h1

theorem id7ChkCv_of_pinned
    (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
      lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
    (hw0 : wt 0 = 1) : id7ChkCv = true := by
  have hK := id7ChkCvK_ok
  simp only [id7ChkCvK, id7CvChkG, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true] at hK
  obtain ⟨⟨⟨hlen, -⟩, hgen⟩, hm⟩ := hK
  have hg : ∀ g ∈ id7CvGens.toList, id7CvGenOK g = true ∧
      decode32 (id7VecK g.1 g.2.1 (2 ^ g.2.2)) = decode32 (id7CvVec g) := by
    intro g hg'
    have h := hgen g hg'
    simp only [id7CvGenK, id7FLineK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    obtain ⟨hl1, hl2⟩ := hL _ _ h1 h2 h5
    refine ⟨?_, id7Vec_decode hl2 (id7VecOK_sound h7).2⟩
    simp only [id7CvGenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hl1⟩, h6⟩
  have hproj : ∀ w, id7CvProj w = id7CvProjK id7CvGens.toList id7CvDual w := by
    intro w
    unfold id7CvProj id7CvProjK
    refine foldl_range_congr (fun acc t ht => ?_) 0
    have ht' : t < id7CvGens.toList.length := by rw [hlen]; exact ht
    have e1 : id7CvVecs[t]! = id7CvVec id7CvGens.toList[t] := getElem!_array_map ht'
    have e2 : (id7CvVecsK id7CvGens.toList)[t]! =
        id7VecK id7CvGens.toList[t].1 id7CvGens.toList[t].2.1 (2 ^ id7CvGens.toList[t].2.2) :=
      getElem!_toArray_map ht'
    rw [e1, e2, fB_congr (hg _ (List.getElem_mem ht')).2 w]
  unfold id7ChkCv
  simp only [Bool.and_eq_true, beq_iff_eq, ← Array.all_toList, List.all_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨rfl, rfl⟩, fun g hg' => (hg g hg').1⟩, fun m hm' => ?_⟩
  rw [hproj, hw0]
  exact hm m hm'

theorem id7ChkQa_of_pinned
    (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
      lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
    (hwt : ∀ j (hj : j < J.wtC.flatten.length), wt j = J.wtC.flatten[j])
    (hidx : ∀ x, wtIdx x < 75735 ↔ wtTree.memB x = true) : id7ChkQa = true := by
  obtain ⟨-, hlen, hfind, hval⟩ := SmithD6Trees.wt_facts
  obtain ⟨h0l, h0⟩ := wt0_pinned
  have hw0 : wt 0 = 1 := by rw [hwt 0 h0l, h0]
  have hH := id7QaHeadK_ok
  simp only [id7QaHeadK, id7QaHeadG, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hH
  obtain ⟨⟨⟨⟨hglen, -⟩, hgen⟩, -⟩, hdual⟩ := hH
  have hg : ∀ g ∈ id7QaGens.toList, id7QaGenOK g = true ∧
      id7VecK g.1 g.2.1 (id7WtK g.2.2) = id7QaVec g := by
    intro g hg'
    have h := hgen g hg'
    simp only [id7QaGenK, id7FLineK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
    obtain ⟨hl1, hl2⟩ := hL _ _ h1 h2 h5
    obtain ⟨hk, hs⟩ := hval _ _ (Nat.eq_of_beq_eq_true h7)
    have hwk : wt g.2.2 = id7WtK g.2.2 := by rw [hwt _ hk, hs]
    refine ⟨?_, ?_⟩
    · simp only [id7QaGenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true']
      refine ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hl1⟩, h6⟩, ?_⟩
      rw [hw0, hwk]
      exact h9
    · rw [id7Vec_eq hl2 h10 h8]
      unfold id7QaVec
      rw [hwk]
  have hvec : ∀ t < 16, id7QaVecs[t]! = (id7QaVecsK id7QaGens.toList)[t]! := by
    intro t ht
    have ht' : t < id7QaGens.toList.length := by rw [hglen]; exact ht
    have e1 : id7QaVecs[t]! = id7QaVec id7QaGens.toList[t] := getElem!_array_map ht'
    have e2 : (id7QaVecsK id7QaGens.toList)[t]! = id7VecK id7QaGens.toList[t].1
        id7QaGens.toList[t].2.1 (id7WtK id7QaGens.toList[t].2.2) := getElem!_toArray_map ht'
    rw [e1, e2, (hg _ (List.getElem_mem ht')).2]
  have hproj : ∀ w, id7Proj w = id7ProjP id7QaPairs w := by
    intro w
    rw [← Nat.zero_xor (id7ProjP id7QaPairs w), ← foldl_id7ProjP, id7QaPairs, List.foldl_map]
    unfold id7Proj
    refine foldl_range_congr (fun acc t ht => ?_) 0
    try dsimp only
    rw [fB_eq_fBK, hvec t ht]
  have hwl : J.wtC.length = 37 := by rw [← lenC_eq, SmithD6Trees.wtC_lenC]
  have hstream : ∀ s ∈ J.wtC.flatten, id7QaWtOK id7QaPairs s = true := by
    intro s hs
    obtain ⟨l, hl, hs⟩ := List.mem_flatten.1 hs
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hl
    have h := id7QaChunks_ok c (lt_of_lt_of_eq hc hwl)
    rw [id7QaChunkOK, nthC_eq, getD_eq hc] at h
    exact id7QaGo_sound _ h s hs
  unfold id7ChkQa
  simp only [Bool.and_eq_true, beq_iff_eq, ← Array.all_toList, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨⟨rfl, rfl⟩, fun g hg' => (hg g hg').1⟩, fun s hs t ht => ?_⟩, fun j hj => ?_⟩
  · rw [hvec s hs]
    exact hdual s (List.mem_range.2 hs) t (List.mem_range.2 ht)
  · have hj' : j < J.wtC.flatten.length := by rw [hlen]; exact hj
    have hs := hstream _ (List.getElem_mem hj')
    unfold adjW
    rw [hw0, hwt j hj', hproj, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, hidx]
    rw [← id7QaWtOK_sound hs, eq_comm (a := 1)]

end CertificateChecks.SmithD6Id

end
