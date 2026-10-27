module

public import Certificates.Kernel.SmithD6Ea.Glue
import all Certificates.Data.SmithD6Model

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Ea

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Nc
  CFSG.KD.SmithD6ST CFSG.KD.SmithD6Ea CFSG.KD.SmithD6Reps CertificateChecks.SmithD6Stab
  CertificateChecks.SmithD6Nc CertificateChecks.SmithD6Trees

theorem tvCols_eqP (k : Nat) : tvCols k = tvColsP (linePair k) := rfl

theorem eaF4_facts : JEA.eaQ.length = 1578 ∧
    (∀ k ∈ JEA.eaQ, lineTree.memB k = true ∧ eaInK k = true) ∧ (JEA.eaQ.map eaF).Nodup := by
  have h := f4_ok
  unfold eaF4OK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := eaF4Go_sound _ _ h.2
  exact ⟨h.1, fun k hk => ⟨(h1 k hk).1, (h1 k hk).2.1⟩, h2.imp Nat.ne_of_lt⟩

theorem aK_facts : ∀ x ∈ eaAK, lineTree.memB x = true ∧ ea7IsA (posK x) = true := by
  decide +kernel

theorem odd_keys : posK 4224 = 31 ∧ posK 8256 = 557 ∧ posK 12480 = 1083 ∧
    posK 2230296 = 142115 ∧ lineTree.memB 4224 = true ∧ lineTree.memB 8256 = true ∧
    lineTree.memB 12480 = true ∧ lineTree.memB 2230296 = true ∧ eaInK 4224 = true ∧
    eaInK 8256 = true ∧ eaInK 12480 = true ∧ eaInK 2230296 = true ∧
    imgOK 8256 4224 = true ∧ imgKey 8256 4224 = 12480 ∧
    imgOK 12480 4224 = true ∧ imgKey 12480 4224 = 8256 := by decide +kernel

theorem key_at {k p : Nat} (hm : lineTree.memB k = true) (hp : posK k = p) :
    J.lineKeysC.flatten[p]! = k := by
  rw [← hp]
  exact (key_of_memB hm).2

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
  (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
  (hI : ∀ u w, lineIdx u w < 365211 → lineKeys[lineIdx u w]! = 4096 * u + w)
include hK hL hI

theorem eaQ_cover : ∀ p ∈ ea7I, ∃ k ∈ JEA.eaQ, lineTree.memB k = true ∧ posK k = p := by
  obtain ⟨hlen, hall, hnd⟩ := eaF4_facts
  have hsub : JEA.eaQ.map posK ⊆ ea7I := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
    obtain ⟨hm, hi⟩ := hall k hk
    obtain ⟨hlt, hkey⟩ := key_of_memB hm
    rw [mem_ea7I_iff hK hL hI, hkey]
    exact ⟨hlt, hi⟩
  have hnd' : (JEA.eaQ.map posK).Nodup := by
    refine List.Nodup.map_on ?_ (List.Nodup.of_map eaF hnd)
    intro a ha b hb hab
    exact posK_inj (hall a ha).1 (hall b hb).1 hab
  have hperm := (hnd'.subperm hsub).perm_of_length_le
    (Nat.le_of_eq (by rw [ea7I_length hK hL hI, List.length_map, hlen]))
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hp)
  exact ⟨k, hk, (hall k hk).1, rfl⟩

theorem ea7Restr_eq (p : Nat) : ea7Restr p = eaRestr (pairK J.lineKeysC.flatten[p]!) := by
  unfold ea7Restr eaRestr
  rw [tvCols_eqP, linePair_eq hK]

theorem ea7ChkF4_of_pinned : ea7ChkF4 = true := by
  obtain ⟨-, hall, hnd⟩ := eaF4_facts
  have key : ∀ a ∈ ea7I, ∀ b ∈ ea7I, ea7Restr a = ea7Restr b → a = b := by
    intro a ha b hb hr
    obtain ⟨ka, hka, hma, rfl⟩ := eaQ_cover hK hL hI a ha
    obtain ⟨kb, hkb, hmb, rfl⟩ := eaQ_cover hK hL hI b hb
    rw [ea7Restr_eq hK hL hI, ea7Restr_eq hK hL hI, (key_of_memB hma).2,
      (key_of_memB hmb).2] at hr
    have e := List.inj_on_of_nodup_map hnd hka hkb (by unfold eaF; rw [hr])
    rw [e]
  unfold ea7ChkF4
  simp only [List.all_eq_true, List.mem_map]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr fun hr => h (key a ha b hb hr)

theorem ea7F3_of_pinned (hwt : ∀ j (hj : j < J.wtC.flatten.length), wt j = J.wtC.flatten[j]) :
    ∀ p ∈ ea7I, ∃ i < 75735, applyCols (tvCols 0) (wt i) = wt i ∧
      applyCols (tvCols 31899) (wt i) = wt i ∧
      ∃ c < 2 ^ 32, applyCols (tvCols p) c ^^^ c = wt i := by
  have h := f3_ok
  unfold eaF3All at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  intro p hp
  obtain ⟨k, hk, hm, rfl⟩ := eaQ_cover hK hL hI p hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk
  have hj' : j < JEA.eaF3.length := hlen ▸ hj
  have hz : (JEA.eaQ[j], JEA.eaF3[j]) ∈ JEA.eaQ.zip JEA.eaF3 := by
    have hjz : j < (JEA.eaQ.zip JEA.eaF3).length := by
      rw [List.length_zip]
      exact Nat.lt_min.2 ⟨hj, hj'⟩
    have := List.getElem_mem hjz
    rwa [List.getElem_zip] at this
  have h3 := hall _ hz
  unfold eaF3OK at h3
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
  obtain ⟨⟨⟨⟨hs, h0⟩, h31⟩, hc⟩, hT⟩ := h3
  unfold KT.memB at hs
  obtain ⟨v, hv⟩ : ∃ v, wtTree.find (JEA.eaF3[j].getD 0 0) = v + 1 :=
    Nat.exists_eq_add_one.mpr (by simpa [Nat.blt_eq] using hs)
  obtain ⟨hvl, hx⟩ := wt_facts.2.2.2 _ _ hv
  have hw : wt v = JEA.eaF3[j].getD 0 0 := by rw [hwt v hvl, hx]
  have hvlt : v < 75735 := by
    have := wt_facts.2.1
    omega
  refine ⟨v, hvlt, ?_, ?_, JEA.eaF3[j].getD 1 0, by simpa using hc, ?_⟩
  · rw [hw, tvCols_eqP, linePair_zero hK hL hI]
    exact h0
  · rw [hw, tvCols_eqP, linePair_31899 hK hL hI]
    exact h31
  · rw [hw, tvCols_eqP, linePair_posK hK hL hm]
    exact hT

theorem ea7OddA_of_pinned : ea7I.length = 1578 ∧
    (∀ q ∈ ea7I, ∀ a, ea7IsA a = true → ea7IsA (tvImg q a) = true) ∧
    ea7InX 31 = true ∧ ea7InX 557 = true ∧ ea7InX 1083 = true ∧
    tvImg 557 31 = 1083 ∧ tvImg 1083 31 = 557 ∧
    ea7InX ea7Bases[0]! = true ∧ ea7IsA ea7Bases[0]! = false := by
  obtain ⟨p31, p557, p1083, pb, m31, m557, m1083, mb, i31, i557, i1083, ib, ok1, k1, ok2, k2⟩ :=
    odd_keys
  have hA := a_ok
  unfold eaAOK at hA
  simp only [List.all_eq_true] at hA
  have hX : ∀ {k p : Nat}, lineTree.memB k = true → posK k = p → eaInK k = true →
      ea7InX p = true := by
    intro k p hm hp hi
    rw [ea7InX_eq hK hL hI, key_at hm hp, hi, ← hp, decide_eq_true (key_of_memB hm).1]
    rfl
  refine ⟨ea7I_length hK hL hI, ?_, hX m31 p31 i31, hX m557 p557 i557, hX m1083 p1083 i1083,
    ?_, ?_, ?_, by decide⟩
  · intro q hq a ha
    obtain ⟨kq, hkq, hmq, rfl⟩ := eaQ_cover hK hL hI q hq
    obtain ⟨hql, hqk⟩ := key_of_memB hmq
    have hqb : kq < 16777216 := by
      have := key_lt hql
      rwa [hqk] at this
    have step : ∀ ka ∈ eaAK, ea7IsA (tvImg (posK kq) (posK ka)) = true := by
      intro ka hka
      have hc := hA kq hkq ka hka
      rw [imgN_eq] at hc
      have hmem : imgKey kq ka ∈ eaAK := by simpa using hc
      obtain ⟨hma, -⟩ := aK_facts ka hka
      obtain ⟨hal, hak⟩ := key_of_memB hma
      have hab : ka < 16777216 := by
        have := key_lt hal
        rwa [hak] at this
      obtain ⟨hmi, hia⟩ := aK_facts _ hmem
      have e := (tvImg_eq hK hL hmq hma (imgOK_of hqb hab hmi)).1
      rw [e]
      exact hia
    have hcases : a = 31 ∨ a = 557 ∨ a = 1083 := by
      simpa [ea7IsA, Bool.or_eq_true, beq_iff_eq, or_assoc] using ha
    rcases hcases with rfl | rfl | rfl
    · rw [← p31]
      exact step 4224 (by decide)
    · rw [← p557]
      exact step 8256 (by decide)
    · rw [← p1083]
      exact step 12480 (by decide)
  · have e := (tvImg_eq hK hL m557 m31 ok1).1
    rw [p557, p31, k1, p1083] at e
    exact e
  · have e := (tvImg_eq hK hL m1083 m31 ok2).1
    rw [p1083, p31, k2, p557] at e
    exact e
  · have h0 : ea7Bases[0]! = 142115 := rfl
    rw [h0]
    exact hX mb pb ib

end Model

end CertificateChecks.SmithD6Ea

end
