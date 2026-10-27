module

public import Certificates.Kernel.U43.Checks
public import CFSG.Certificates.Kernel.U43.Sound

public section

namespace CFSG.KC.U43

open CFSG.KC.Loop CFSG.KC.Misc.G2U CFSG.KD.U43 CFSG.KD.G2Three CFSG.KC.G2Three
  CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec4.Item434RemU43

theorem uGens_dat : ∀ s < 3, Dat (uGens.getD s one4) (UG s) := by
  intro s hs
  have e := Nat.eq_of_beq_eq_true (allBelow_g2 u43Gens_ok (by decide) s hs)
  have hl : s < uGenWords.length := by
    have : uGenWords.length = 3 := rfl
    omega
  have hg : uGens = uGenWords.map wordCode := rfl
  have hw : uGens.getD s one4 = wordCode (uGenWords.getD s []) := by
    rw [hg, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map,
      List.getD_eq_getElem _ _ hl]
  rw [hw, e]
  exact wordD u43Letters_ok _

theorem uTable : uElems.size = 729 ∧ ∀ t < 729, Dat (uElems.getD t one4) (UX t) := by
  have hpl : uPar.length = 728 := by decide +kernel
  unfold uElems build
  have key := build_par (X := UX) uGens_dat uPar #[one4] 0 rfl (fun t ht => by
    have : t = 0 := by omega
    subst this
    exact ⟨canon4_one4, (Nat.eq_of_beq_eq_true u43One_ok).symm⟩) u43Par_ok
  rw [hpl] at key
  exact ⟨key.1, key.2⟩

theorem datAt {t : ℕ} (ht : t < 729) : Dat (uAt t) (UX t) := by
  unfold uAt
  rw [getD_irrel (by rw [uTable.1]; exact ht) [] one4]
  exact uTable.2 t ht

theorem uX_inj : ∀ t < 729, ∀ t' < 729, UX t = UX t' → t = t' :=
  sort_inj u43Sort_ok (by decide)

theorem uElems_inj {t t' : ℕ} (ht : t < uElems.size) (ht' : t' < uElems.size)
    (h : uElems.getD t [] = uElems.getD t' []) : t = t' := by
  rw [uTable.1] at ht ht'
  have a := datAt ht
  have b := datAt ht'
  unfold uAt at a b
  exact uX_inj t ht t' ht' (by rw [← a.2, ← b.2, h])

theorem uSylCheck_kc : uSylCheck = true := by
  have hk : (List.range 2187).length = 729 * 3 := by simp
  have hcl := close_at4 u43Close_ok (by decide)
  unfold uSylCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨by rw [uTable.1]; rfl, closedCheck_of fun v hv g hg => ?_⟩,
    distinctCheck_of fun t ht t' ht' h => uElems_inj ht ht' h⟩,
    allCheck_of fun t ht => ?_⟩, by decide⟩
  · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg
    have hs3 : s < 3 := by
      have : uGens.length = 3 := rfl
      omega
    rw [uTable.1] at hv
    obtain ⟨hi, hdiv, hmod⟩ := flat_facts (by decide : 0 < 3) hv hs3
    obtain ⟨hp, hx⟩ := hcl _ hi
    rw [hdiv, hmod] at hx
    refine ⟨fR (UPOS 0) (v * 3 + s), by rw [uTable.1]; exact hp, ?_⟩
    have a := datAt hp
    have b := mulD (datAt hv) (uGens_dat s hs3)
    unfold uAt at a b
    rw [← List.getD_eq_getElem _ one4 hs]
    exact inj4 a.1 b.1 (by rw [a.2, b.2, hx])
  · rw [uTable.1] at ht
    exact (datAt ht).1

theorem posOf_at {t : ℕ} (ht : t < 729) : posOf (uAt t) = t := by
  have hs : t < uElems.size := by rw [uTable.1]; exact ht
  have hf : found uElems uIdx (uAt t) = true := found_indexMap.2 ⟨t, hs, rfl⟩
  unfold posOf
  rw [if_pos hf]
  have hsome := indexMap_isSome hs
  cases hm : (indexMap uElems).get? (uElems.getD t []) with
  | none => rw [hm] at hsome; cases hsome
  | some s =>
    obtain ⟨h1, h2⟩ := indexMap_get? hm
    have e : uIdx.get? (uAt t) = some s := hm
    rw [e, Option.getD_some]
    exact uElems_inj h1 hs h2

theorem kind_okc {c : List ℕ} {C w : ℕ} (hc : Dat c C) (h : okc UX w C = true) :
    (c == one4 || kindOf c == 3) = true := by
  unfold okc at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  rcases h with h | ⟨⟨hw, hx⟩, hk⟩
  · rw [beqD hc oneD, h, Nat.beq_refl, Bool.true_or]
  · have hd := datAt hw
    have e : c = uAt w := inj4 hc.1 hd.1 (by rw [hc.2, hd.2, hx])
    unfold kindOf
    rw [e, posOf_at hw, hk]
    simp

theorem e9D {a b : List ℕ} {A B o : ℕ} (ha : Dat a A) (hb : Dat b B)
    (h : e9K UX UKW A B o = true) :
    (e9Elems a b).all (fun c => c == one4 || kindOf c == 3) = true := by
  unfold e9K at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have sa : Dat (sq4 a) (M4 A A) := mulD ha ha
  have sb : Dat (sq4 b) (M4 B B) := mulD hb hb
  unfold e9Elems
  rw [← Array.all_toList, List.toList_toArray]
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.all_cons, List.all_nil, Bool.and_true,
    kind_okc (mulD oneD oneD) h0, kind_okc (mulD oneD hb) h1, kind_okc (mulD oneD sb) h2,
    kind_okc (mulD ha oneD) h3, kind_okc (mulD ha hb) h4, kind_okc (mulD ha sb) h5,
    kind_okc (mulD sa oneD) h6, kind_okc (mulD sa hb) h7, kind_okc (mulD sa sb) h8]

theorem tri_lt {l : List ℕ} (hl : (l.length == 3) = true) (ha : l.all (· < 729) = true) {i : ℕ}
    (hi : i < 3) : l.getD i 0 < 729 := by
  have hl' : l.length = 3 := by simpa using hl
  rw [List.all_eq_true] at ha
  rw [List.getD_eq_getElem _ _ (by omega)]
  simpa using ha _ (List.getElem_mem (by omega))

theorem badOK_of (hall : ∀ k < 12, badK UX UA UKW k = true) {k : ℕ} (hk : k < 12) :
    badOK k = true := by
  have hD : ∀ k < 12, badDK k = true := fun k hk => by
    have := hall k hk
    unfold badK at this
    simp only [Bool.and_eq_true] at this
    exact this.1
  have hP := hall k hk
  unfold badK at hP
  rw [Bool.and_eq_true] at hP
  have hPk := hP.2
  have hDk := hD k hk
  unfold badDK at hDk
  simp only [Bool.and_eq_true] at hDk
  obtain ⟨⟨⟨⟨d1, d2⟩, d3⟩, d4⟩, d5⟩ := hDk
  have hr : repIdx (badClass k) < 12 := by simpa using d4
  have hDr := hD _ hr
  unfold badDK at hDr
  simp only [Bool.and_eq_true] at hDr
  obtain ⟨⟨⟨⟨r1, r2⟩, -⟩, -⟩, -⟩ := hDr
  have ha : Dat (badA k) (UX ((badTriple k).getD 1 0)) := datAt (tri_lt d1 d2 (by decide))
  have hb : Dat (badB k) (UX ((badTriple k).getD 2 0)) := datAt (tri_lt d1 d2 (by decide))
  have hra : Dat (badA (repIdx (badClass k)))
      (UX ((badTriple (repIdx (badClass k))).getD 1 0)) := datAt (tri_lt r1 r2 (by decide))
  have hrb : Dat (badB (repIdx (badClass k)))
      (UX ((badTriple (repIdx (badClass k))).getD 2 0)) := datAt (tri_lt r1 r2 (by decide))
  have hz : Dat zc (UX uZ) := datAt (by decide)
  have hz2 : Dat zc2 (M4 (UX uZ) (UX uZ)) := mulD hz hz
  have hsa : Dat (sq4 (badA k)) (M4 (UX ((badTriple k).getD 1 0)) (UX ((badTriple k).getD 1 0))) :=
    mulD ha ha
  unfold badPK at hPk
  simp only [Bool.and_eq_true] at hPk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩, p8⟩, p9⟩ := hPk
  have c1 : commutes4 (badA k) (badB k) = true := by rw [commD ha hb]; exact p1
  have c2 : (cube4 (badA k) == one4) = true := by rw [cubeD ha]; exact p2
  have c3 : (cube4 (badB k) == one4) = true := by rw [cubeD hb]; exact p3
  have c4 : (badA k == one4) = false := by
    rw [beqD ha oneD]
    simpa using p4
  have c5 : [one4, badA k, sq4 (badA k)].contains (badB k) = false := by
    rw [List.contains_cons, List.contains_cons, List.contains_cons, List.contains_nil,
      beqD hb oneD, beqD hb ha, beqD hb hsa, Bool.or_false, ← Bool.or_assoc]
    simpa only [Bool.not_eq_true'] using p5
  have c6 := e9D ha hb p6
  have c7 : (conjStep (wordPair (badWord k)) (badA k) == badA (repIdx (badClass k))) = true := by
    rw [beqD (conjD u43Letters_ok _ ha) hra]
    exact p7
  have c8 : (conjStep (wordPair (badWord k)) (badB k) == badB (repIdx (badClass k))) = true := by
    rw [beqD (conjD u43Letters_ok _ hb) hrb]
    exact p8
  have c9 : (conjStep (wordPair (badWord k)) zc == zc ||
      conjStep (wordPair (badWord k)) zc == zc2) = true := by
    rw [beqD (conjD u43Letters_ok _ hz) hz, beqD (conjD u43Letters_ok _ hz) hz2]
    exact p9
  unfold badOK
  rw [d1, d2, d3, d4, d5, c1, c2, c3, c4, c5, c6, c7, c8, c9]
  rfl

theorem uBadCheck_kc : uBadCheck = true := by
  have hall : ∀ k < 12, badK UX UA UKW k = true := allBelow_g2 u43Bad_ok (by decide)
  unfold uBadCheck
  rw [Bool.and_eq_true]
  exact ⟨rfl, all_range_of fun k hk => badOK_of hall hk⟩

end CFSG.KC.U43

end
