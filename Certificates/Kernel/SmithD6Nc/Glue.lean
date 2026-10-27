module

public import Certificates.Kernel.SmithD6Nc.Checks
public import Certificates.Kernel.SmithD6Stab.Glue
import all Certificates.Data.SmithD6Model
import all Certificates.Data.SmithD6Stab

public section

namespace CertificateChecks.SmithD6Nc

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Nc
  CertificateChecks.SmithD6Stab CertificateChecks.SmithD6Trees

@[expose] noncomputable def posK (k : Nat) : Nat := lineTree.find k - 1

theorem key_of_memB {k : Nat} (h : lineTree.memB k = true) :
    posK k < 365211 ∧ J.lineKeysC.flatten[posK k]! = k := by
  have hpos : 0 < lineTree.find k := Nat.le_of_ble_eq_true h
  exact key_of_find (x := k) (v := posK k) (by unfold posK; omega)

theorem posK_inj {a b : Nat} (ha : lineTree.memB a = true) (hb : lineTree.memB b = true)
    (h : posK a = posK b) : a = b := by
  have h1 := (key_of_memB ha).2
  rw [h, (key_of_memB hb).2] at h1
  exact h1.symm

theorem posK_base : posK 4098 = 0 ∧ lineTree.memB 4098 = true := by
  obtain ⟨-, hn, hf, -⟩ := lineKeys_facts
  have h0 : 0 < J.lineKeysC.flatten.length := by rw [hn]; decide
  have h := hf 0 h0
  rw [← getElem!_pos J.lineKeysC.flatten 0 h0, key_zero] at h
  refine ⟨by unfold posK; rw [h], ?_⟩
  simp only [KT.memB, h]
  rfl

theorem rootLines_eq : rootLines = (rootPairs.map fun p => lineOf p.1 p.2).toArray := by
  unfold rootLines rootPairs
  simp only [List.map_flatMap, apply_ite (List.map _), List.map_cons, List.map_nil]

theorem nc_facts :
    (∀ p ∈ rootPairs, key3OK p.1 p.2 (p.1 ^^^ p.2) = true ∧ imgOK (pairKey p) 4098 = true) ∧
    stabKeys.length = 42 ∧ imgOK (stabKeys.getD 0 0) (stabKeys.getD 1 0) = true ∧
    imgKey (stabKeys.getD 0 0) (stabKeys.getD 1 0) ≠ stabKeys.getD 1 0 := by
  have h := nc_ok
  simp only [ncOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
  (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
include hK hL

theorem lineIdx_eq {u w : Nat} (hu : u < 4096) (hw : w < 4096)
    (h : lineTree.memB (4096 * u + w) = true) : lineIdx u w = posK (4096 * u + w) := by
  obtain ⟨hlt, hp⟩ := hL u w hu hw h
  have hk : J.lineKeysC.flatten[lineIdx u w]! = 4096 * u + w := by
    have e := linePair_eq hK (a := lineIdx u w)
    rw [hp] at e
    simp only [pairK, Prod.mk.injEq] at e
    omega
  obtain ⟨-, hn, hf, -⟩ := lineKeys_facts
  have hlt' : lineIdx u w < J.lineKeysC.flatten.length := hn ▸ hlt
  have e := hf _ hlt'
  rw [← getElem!_pos J.lineKeysC.flatten _ hlt', hk] at e
  unfold posK
  omega

theorem lineIdx3_eq {x y z : Nat} (h : key3OK x y z = true) :
    lineIdx3 x y z = posK (key3 x y z) ∧ lineTree.memB (key3 x y z) = true := by
  simp only [key3OK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨lineIdx_eq hK hL h1 h2 h3, h3⟩

theorem linePair_posK {k : Nat} (h : lineTree.memB k = true) : linePair (posK k) = pairK k := by
  rw [linePair_eq hK, (key_of_memB h).2]

theorem tvImg_eq {a b : Nat} (ha : lineTree.memB a = true) (hb : lineTree.memB b = true)
    (h : imgOK a b = true) :
    tvImg (posK a) (posK b) = posK (imgKey a b) ∧ lineTree.memB (imgKey a b) = true := by
  have e := lineIdx3_eq hK hL h
  unfold tvImg
  rw [linePair_posK hK hL ha, linePair_posK hK hL hb]
  exact e

theorem stabGens_eq : stabGens = (stabKeys.map posK).toArray := by
  obtain ⟨hroot, -, -, -⟩ := nc_facts
  obtain ⟨hb0, hbm⟩ := posK_base
  have hmem : ∀ k ∈ rootPairs.map pairKey, lineTree.memB k = true ∧ imgOK k 4098 = true := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
    exact ⟨(lineIdx3_eq hK hL (hroot p hp).1).2, (hroot p hp).2⟩
  have hroots : rootLines = ((rootPairs.map pairKey).map posK).toArray := by
    rw [rootLines_eq, List.map_map]
    apply congrArg List.toArray
    apply List.map_congr_left
    intro p hp
    exact (lineIdx3_eq hK hL (hroot p hp).1).1
  unfold stabGens stabKeys
  rw [hroots, List.filter_toArray, List.filter_map]
  apply congrArg List.toArray
  apply congrArg (List.map posK)
  apply List.filter_congr
  intro k hk
  obtain ⟨hm, hi⟩ := hmem k hk
  obtain ⟨himg, himgm⟩ := tvImg_eq hK hL hm hbm hi
  simp only [Function.comp_apply]
  rw [← hb0, himg]
  have e1 : (posK k != posK 4098) = (k != 4098) := by
    apply Bool.eq_iff_iff.2
    simp only [bne_iff_ne, ne_eq]
    exact ⟨fun h h' => h (by rw [h']), fun h h' => h (posK_inj hm hbm h')⟩
  have e2 : (posK (imgKey k 4098) == posK 4098) = (imgKey k 4098 == 4098) := by
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq]
    exact ⟨fun h => posK_inj himgm hbm h, fun h => by rw [h]⟩
  rw [e1, e2]

theorem chkStabNc_of_pinned : chkStabNc = true := by
  obtain ⟨hroot, hlen, hi, hne⟩ := nc_facts
  have hmem : ∀ k ∈ stabKeys, lineTree.memB k = true := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hk).1
    exact (lineIdx3_eq hK hL (hroot p hp).1).2
  have h0 : 0 < stabKeys.length := by omega
  have h1 : 1 < stabKeys.length := by omega
  have hs : (stabKeys.map posK).toArray.size = stabKeys.length := by
    simp only [List.size_toArray, List.length_map]
  have g0 : stabGens[0]! = posK (stabKeys.getD 0 0) := by
    rw [stabGens_eq hK hL, getElem!_pos _ 0 (by omega), getD_eq h0]
    simp only [List.getElem_toArray, List.getElem_map]
  have g1 : stabGens[1]! = posK (stabKeys.getD 1 0) := by
    rw [stabGens_eq hK hL, getElem!_pos _ 1 (by omega), getD_eq h1]
    simp only [List.getElem_toArray, List.getElem_map]
  have m0 : lineTree.memB (stabKeys.getD 0 0) = true := by
    rw [getD_eq h0]
    exact hmem _ (List.getElem_mem h0)
  have m1 : lineTree.memB (stabKeys.getD 1 0) = true := by
    rw [getD_eq h1]
    exact hmem _ (List.getElem_mem h1)
  obtain ⟨himg, himgm⟩ := tvImg_eq hK hL m0 m1 hi
  unfold chkStabNc
  rw [g0, g1, himg, stabGens_eq hK hL]
  simp only [List.size_toArray, List.length_map, hlen, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq, true_and]
  exact fun h => hne (posK_inj himgm m1 h)

end Model

end CertificateChecks.SmithD6Nc

end
