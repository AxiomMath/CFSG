module

public import Certificates.Kernel.SmithD6Ea.Checks
public import Certificates.Kernel.SmithD6Nc.Glue
public import CFSG.Certificates.Kernel.SmithD6EaSound
import all Certificates.Data.SmithD6Model
public import CFSG.Certificates.Kernel.SmithD6StabTreeSound

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Ea

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Nc
  CFSG.KD.SmithD6ST CFSG.KD.SmithD6Ea CFSG.KD.SmithD6Reps CertificateChecks.SmithD6Stab
  CertificateChecks.SmithD6Nc CertificateChecks.SmithD6Trees

theorem keyAt_eq {p : Nat} (hp : p < 365211) : J.lineKeysC.flatten[p]! = keyAt p := by
  have hl : J.lineKeysC.length = 179 := by rw [← lenC_eq, lineKeysC_lenC]
  have hc : p / 2048 < J.lineKeysC.length := by rw [hl]; omega
  have hc179 : p / 2048 < 179 := by rw [hl] at hc; exact hc
  obtain ⟨hf, hlen, -⟩ := chunkOK_sound hc (lineChunks_ok (p / 2048) hc179)
  have hj : p % 2048 < J.lineKeysC[p / 2048].length := by
    rw [hl] at hlen
    split_ifs at hlen with h <;> omega
  have hfi := hf (p % 2048) hj
  have hi' : 2048 * (p / 2048) + p % 2048 = p := Nat.div_add_mod p 2048
  rw [hi'] at hfi
  obtain ⟨hv, hx⟩ := lineKeys_facts.2.2.2 _ _ hfi
  rw [getElem!_pos _ p hv, hx, keyAt, nthC_eq, getD_eq hc]
  exact (getD_eq hj).symm

theorem key_31899 : J.lineKeysC.flatten[31899]! = 262272 := by
  rw [keyAt_eq (by decide)]
  decide +kernel

theorem key_last : J.lineKeysC.flatten[365210]! = 8383486 := by
  rw [keyAt_eq (by decide)]
  decide +kernel

theorem key_lt {p : Nat} (hp : p < 365211) : J.lineKeysC.flatten[p]! < 16777216 := by
  obtain ⟨hs, hn, -, -⟩ := lineKeys_facts
  have hp' : p < J.lineKeysC.flatten.length := hn ▸ hp
  have hl' : 365210 < J.lineKeysC.flatten.length := by rw [hn]; decide
  have e := key_last
  rw [getElem!_pos J.lineKeysC.flatten 365210 hl'] at e
  rw [getElem!_pos J.lineKeysC.flatten p hp']
  rcases Nat.lt_or_ge p 365210 with h | h
  · have := List.pairwise_iff_getElem.1 hs p 365210 hp' hl' h
    omega
  · have : p = 365210 := by omega
    subst this
    omega

theorem find_key {p : Nat} (hp : p < 365211) :
    lineTree.memB J.lineKeysC.flatten[p]! = true ∧ posK J.lineKeysC.flatten[p]! = p := by
  obtain ⟨-, hn, hf, -⟩ := lineKeys_facts
  have hp' : p < J.lineKeysC.flatten.length := hn ▸ hp
  have h := hf p hp'
  rw [← getElem!_pos J.lineKeysC.flatten p hp'] at h
  refine ⟨?_, ?_⟩
  · simp only [KT.memB, h]
    rfl
  · unfold posK
    rw [h]
    rfl

theorem xor_lt4096 {x y : Nat} (hx : x < 4096) (hy : y < 4096) : x ^^^ y < 4096 :=
  Nat.xor_lt_two_pow (n := 12) hx hy

theorem sglK_lt {u w x : Nat} (hu : u < 4096) (hw : w < 4096) (hx : x < 4096) :
    sglK u w x < 4096 := by
  unfold sglK
  apply xor_lt4096 (xor_lt4096 hx ?_) ?_
  · split_ifs
    · exact hu
    · decide
  · split_ifs
    · exact hw
    · decide

theorem key3OK_of {x y : Nat} (hx : x < 4096) (hy : y < 4096)
    (hm : lineTree.memB (key3 x y (x ^^^ y)) = true) : key3OK x y (x ^^^ y) = true := by
  have hz := xor_lt4096 hx hy
  have hlo : min x (min y (x ^^^ y)) < 4096 := lt_of_le_of_lt (min_le_left _ _) hx
  have hhi : max x (max y (x ^^^ y)) < 4096 := max_lt hx (max_lt hy hz)
  unfold key3 at hm
  unfold key3OK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hlo, xor_lt4096 hlo hhi⟩, hm⟩

theorem imgOK_of {a b : Nat} (ha : a < 16777216) (hb : b < 16777216)
    (hm : lineTree.memB (imgKey a b) = true) : imgOK a b = true := by
  have hu : (pairK a).1 < 4096 := by simp only [pairK]; omega
  have hw : (pairK a).2 < 4096 := Nat.mod_lt _ (by decide)
  have hbu : (pairK b).1 < 4096 := by simp only [pairK]; omega
  have hbw : (pairK b).2 < 4096 := Nat.mod_lt _ (by decide)
  exact key3OK_of (sglK_lt hu hw hbu) (sglK_lt hu hw hbw) hm

theorem eaKC_eq : JEA.eaKC = J.lineKeysC.map (List.filter eaInK) := by
  have hl : J.lineKeysC.length = 179 := by rw [← lenC_eq, lineKeysC_lenC]
  apply List.ext_getElem (by rw [List.length_map, hl, eaKC_length])
  intro c h1 h2
  have hc : c < 179 := by rw [eaKC_length] at h1; exact h1
  have h := eaGo_sound _ _ (eaChunks_ok c hc)
  rw [nthC_eq, nthC_eq, getD_eq h1, getD_eq (by rw [hl]; exact hc)] at h
  rw [h, List.getElem_map]

theorem cbw_facts : eaPivotP (1, 2) = true ∧ eaPivotP (64, 128) = true ∧
    ((List.range 32).all fun m => ea7Bits.contains m == (eaDiffP (1, 2) m == 0 &&
      eaDiffP (64, 128) m == 0)) = true ∧ (ea7Bits.all fun m => wtTree.memB (2 ^ m)) = true := by
  have h := cbw_ok
  unfold eaCBWOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem ea7Diff_eq (k : Nat) : ea7Diff k = eaDiffP (linePair k) := rfl

theorem ea7Pivot_eq (k : Nat) : ea7Pivot k = eaPivotP (linePair k) := rfl

theorem eaRigP_congr {f : Nat → Bool} {g g' : Nat → Nat × Nat}
    (h : ∀ p ∈ ([0, 31, 557, 1579, 1583, 3675, 1591, 3683, 31899, 3747, 7899, 1655, 7963, 1719,
      3811, 1847, 3939] : List Nat), g p = g' p) :
    eaRigP f g = eaRigP f g' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  simp only [eaRigP, ea7RigData, List.all_cons, List.all_nil, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17]

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
  (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
  (hI : ∀ u w, lineIdx u w < 365211 → lineKeys[lineIdx u w]! = 4096 * u + w)
include hK hL hI

theorem tvImg_key {a b : Nat} (h : tvImg a b < 365211) :
    J.lineKeysC.flatten[tvImg a b]! = imgKey J.lineKeysC.flatten[a]! J.lineKeysC.flatten[b]! := by
  have hk : ∀ i, lineKeys[i]! = J.lineKeysC.flatten[i]! := fun i => by
    rw [← hK, Array.getElem!_toList]
  have e := hI _ _ h
  rw [hk] at e
  refine Eq.trans e ?_
  rw [linePair_eq hK (a := a), linePair_eq hK (a := b)]
  rfl

theorem tvImg_fix_iff {a b : Nat} (ha : a < 365211) (hb : b < 365211) :
    tvImg a b = b ↔ imgKey J.lineKeysC.flatten[a]! J.lineKeysC.flatten[b]! =
      J.lineKeysC.flatten[b]! := by
  obtain ⟨hma, hpa⟩ := find_key ha
  obtain ⟨hmb, hpb⟩ := find_key hb
  constructor
  · intro h
    have hlt : tvImg a b < 365211 := by rw [h]; exact hb
    have e := tvImg_key hK hL hI hlt
    rw [h] at e
    exact e.symm
  · intro h
    have hok : imgOK J.lineKeysC.flatten[a]! J.lineKeysC.flatten[b]! = true :=
      imgOK_of (key_lt ha) (key_lt hb) (by rw [h]; exact hmb)
    have e := (tvImg_eq hK hL hma hmb hok).1
    rw [hpa, hpb, h, hpb] at e
    exact e

theorem tvImg_beq {a b : Nat} (ha : a < 365211) (hb : b < 365211) :
    (tvImg a b == b) = Nat.beq (imgKey J.lineKeysC.flatten[a]! J.lineKeysC.flatten[b]!)
      J.lineKeysC.flatten[b]! := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, tvImg_fix_iff hK hL hI ha hb]

theorem ea7InX_eq (p : Nat) :
    ea7InX p = (decide (p < 365211) && eaInK J.lineKeysC.flatten[p]!) := by
  by_cases hp : p < 365211
  · have h0 := tvImg_beq hK hL hI hp (b := 0) (by decide)
    have h1 := tvImg_beq hK hL hI hp (b := 31899) (by decide)
    rw [key_zero] at h0
    rw [key_31899] at h1
    unfold ea7InX eaInK
    rw [imgN_eq, imgN_eq, h0, h1]
    simp only [hp, decide_true, Bool.true_and]
    generalize Nat.beq (imgKey J.lineKeysC.flatten[p]! 4098) 4098 = x
    generalize Nat.beq (imgKey J.lineKeysC.flatten[p]! 262272) 262272 = y
    cases x <;> cases y <;> rfl
  · unfold ea7InX
    simp [hp]

theorem mem_ea7I_iff {p : Nat} :
    p ∈ ea7I ↔ p < 365211 ∧ eaInK J.lineKeysC.flatten[p]! = true := by
  unfold ea7I
  rw [List.mem_filter, List.mem_range, ea7InX_eq hK hL hI]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

theorem ea7I_map : ea7I.map (fun p => J.lineKeysC.flatten[p]!) = JEA.eaKC.flatten := by
  have hn : J.lineKeysC.flatten.length = 365211 := lineKeys_facts.2.1
  have e1 : ea7I = (List.range J.lineKeysC.flatten.length).filter
      (eaInK ∘ fun p => J.lineKeysC.flatten[p]!) := by
    unfold ea7I
    rw [hn]
    apply List.filter_congr
    intro p hp
    rw [ea7InX_eq hK hL hI, decide_eq_true (List.mem_range.1 hp), Bool.true_and,
      Function.comp_apply]
  have e2 := List.filter_map (f := fun p => J.lineKeysC.flatten[p]!) (p := eaInK)
    (l := List.range J.lineKeysC.flatten.length)
  rw [map_range_getElem!] at e2
  rw [e1, ← e2, List.filter_flatten, eaKC_eq]

theorem ea7I_length : ea7I.length = 1578 := by
  rw [← List.length_map (f := fun p => J.lineKeysC.flatten[p]!), ea7I_map hK hL hI,
    eaKC_flatten_length]

theorem linePair_31899 : linePair 31899 = (64, 128) := by
  rw [linePair_eq hK, key_31899]
  rfl

theorem linePair_zero : linePair 0 = (1, 2) := by
  rw [linePair_eq hK, key_zero]
  rfl

theorem ea7ChkCols_of_pinned : ea7ChkCols = true := by
  unfold ea7ChkCols
  rw [ea7Pivot_eq, ea7Pivot_eq, linePair_zero hK hL hI, linePair_31899 hK hL hI, cbw_facts.1,
    cbw_facts.2.1]
  rfl

theorem ea7ChkBits_of_pinned : ea7ChkBits = true := by
  unfold ea7ChkBits
  rw [ea7Diff_eq, ea7Diff_eq, linePair_zero hK hL hI, linePair_31899 hK hL hI]
  exact cbw_facts.2.2.1

end Model

theorem ea7ChkW_of_pinned (hwt : ∀ j (hj : j < J.wtC.flatten.length), wt j = J.wtC.flatten[j]) :
    ea7ChkW = true := by
  have h := cbw_facts.2.2.2
  unfold ea7ChkW
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq] at h ⊢
  intro m hm
  have hb := h m hm
  unfold KT.memB at hb
  obtain ⟨v, hv⟩ : ∃ v, wtTree.find (2 ^ m) = v + 1 :=
    Nat.exists_eq_add_one.mpr (by simpa [Nat.blt_eq] using hb)
  obtain ⟨hvl, hx⟩ := wt_facts.2.2.2 _ _ hv
  refine ⟨v, ?_, by rw [hwt v hvl, hx]⟩
  have := wt_facts.2.1
  omega

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
  (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
  (hI : ∀ u w, lineIdx u w < 365211 → lineKeys[lineIdx u w]! = 4096 * u + w)
include hK hL hI

theorem ea7InF0_eq : ea7InF0 = eaInF0K := by
  funext p
  unfold ea7InF0 eaInF0K
  rw [ea7InX_eq hK hL hI]
  by_cases hp : p < 365211
  · rw [keyAt_eq hp]
  · simp [hp]

theorem ea7ChkRig_of_pinned : ea7ChkRig = true := by
  have e : ea7ChkRig = eaRigP ea7InF0 linePair := rfl
  rw [e, ea7InF0_eq hK hL hI, eaRigP_congr (g' := fun p => pairK (keyAt p))]
  · exact rig_ok
  · intro p hp
    have hp' : p < 365211 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      omega
    rw [linePair_eq hK, keyAt_eq hp']

end Model

end CertificateChecks.SmithD6Ea

end
