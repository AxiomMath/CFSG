module

public import Certificates.Kernel.G2Three.S7Checks
public import Certificates.Kernel.G2Three.RowsFinal

public section

namespace CFSG.KD.G2Three

open CFSG.KC.G2Three CFSG.RankThree.PartTwo.Census.Carrier.G2Three Certificates.S5RowsG23
  Certificates.S7G23

theorem pkm {a b : List ℕ} (ha : canon14 a = true) (hb : canon14 b = true) :
    pk (mul14 a b) = MUL (pk a) (pk b) :=
  (mulE consts_ok ⟨ha, rfl⟩ ⟨hb, rfl⟩).2

theorem any_congr' {α : Type} {L : List α} {p q : α → Bool} (h : ∀ c ∈ L, p c = q c) :
    L.any p = L.any q := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.any_cons, List.any_cons, h c (by simp), ih fun c' hc' => h c' (by simp [hc'])]

theorem all_congr' {α : Type} {L : List α} {p q : α → Bool} (h : ∀ c ∈ L, p c = q c) :
    L.all p = L.all q := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.all_cons, List.all_cons, h c (by simp), ih fun c' hc' => h c' (by simp [hc'])]

theorem gC_ok (k : ℕ) :
    canon14 (gensC.getD k one14) = true ∧ pk (gensC.getD k one14) = s7Gen GA k := by
  unfold s7Gen
  rcases Nat.lt_or_ge k 4 with hk | hk
  · rw [Nat.blt_eq.mpr hk, cond_true]
    exact gA_ok k hk
  · have hb : Nat.blt k 4 = false := Bool.eq_false_iff.mpr fun h => absurd (Nat.blt_eq.mp h) (by omega)
    rw [hb, cond_false, List.getD_eq_default _ _ (by simp [gensC]; omega)]
    exact ⟨canon14_one14, bone⟩

theorem foldl_pk (w : List ℕ) (f : ℕ → List ℕ) (F : ℕ → ℕ)
    (hf : ∀ k, canon14 (f k) = true ∧ pk (f k) = F k) :
    ∀ acc : List ℕ, canon14 acc = true →
      canon14 (w.foldl (fun acc k => mul14 acc (f k)) acc) = true ∧
        pk (w.foldl (fun acc k => mul14 acc (f k)) acc) = w.foldl (fun A k => MUL A (F k)) (pk acc) := by
  induction w with
  | nil => exact fun acc h => ⟨h, rfl⟩
  | cons k w ih =>
    intro acc h
    have e := ih _ (canon14_mul14 acc (f k))
    rw [pkm h (hf k).1, (hf k).2] at e
    rw [List.foldl_cons, List.foldl_cons]
    exact e

theorem word_pk (w : List ℕ) : canon14 (wordC w) = true ∧ pk (wordC w) = s7Word GA w := by
  have h := foldl_pk w _ _ gC_ok one14 canon14_one14
  rw [bone] at h
  exact h

theorem wordInv_pk (w : List ℕ) :
    canon14 (wordInvC w) = true ∧ pk (wordInvC w) = s7WordInv GA w := by
  have h := foldl_pk w.reverse (fun k => sq14 (gensC.getD k one14))
    (fun k => MUL (s7Gen GA k) (s7Gen GA k))
    (fun k => mulE consts_ok (gC_ok k) (gC_ok k)) one14 canon14_one14
  rw [bone] at h
  exact h

theorem spanC_canon {i j : List ℕ} (hi : canon14 i = true) (hj : canon14 j = true) :
    ∀ c ∈ spanC i j, canon14 c = true := by
  intro c hc
  simp only [spanC, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact canon14_one14
  · exact canon14_mul14 _ _
  · exact hi
  · exact canon14_mul14 _ _
  · exact hj
  · exact canon14_mul14 _ _
  · exact canon14_mul14 _ _
  · exact canon14_mul14 _ _

theorem spanC_map {i j : List ℕ} (hi : canon14 i = true) (hj : canon14 j = true) :
    (spanC i j).map pk = spanK (pk i) (pk j) := by
  simp only [spanC, spanK, sq14, List.map_cons, List.map_nil, pkm (canon14_mul14 i i) hi,
    pkm (canon14_mul14 j j) hj, pkm hi hi, pkm hj hj, pkm hi hj, pkm hj hi, bone]

theorem conjInC_pk {sp : List (List ℕ)} {g x : List ℕ} (hsp : ∀ c ∈ sp, canon14 c = true)
    (hg : canon14 g = true) (hx : canon14 x = true) :
    conjInC sp g x = conjInK (sp.map pk) (pk g) (pk x) := by
  simp only [conjInC, conjInK, List.any_map]
  refine any_congr' fun q hq => ?_
  rw [Function.comp_apply, beq_pk (canon14_mul14 _ _) (canon14_mul14 _ _), pkm hg hx,
    pkm (hsp q hq) hg]

theorem inSpanC_pk {i j x : List ℕ} (hi : canon14 i = true) (hj : canon14 j = true)
    (hx : canon14 x = true) : inSpanC i j x = memK (pk x) (spanK (pk i) (pk j)) := by
  rw [← spanC_map hi hj]
  unfold inSpanC memK
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true]
  constructor
  · intro h
    have hm : x ∈ spanC i j := by simpa using h
    exact ⟨pk x, List.mem_map.2 ⟨x, hm, rfl⟩, Nat.beq_eq.mpr rfl⟩
  · rintro ⟨Y, hY, he⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hY
    have e := pk_inj (spanC_canon hi hj c hc) hx (Nat.eq_of_beq_eq_true he)
    subst e
    simpa using hc

theorem normC_pk {i j g : List ℕ} (hi : canon14 i = true) (hj : canon14 j = true)
    (hg : canon14 g = true) : normC i j g = normK (pk i) (pk j) (pk g) := by
  simp only [normC, normK]
  rw [conjInC_pk (spanC_canon hi hj) hg hi, conjInC_pk (spanC_canon hi hj) hg hj, spanC_map hi hj]

theorem ord4C_pk {u : List ℕ} (hu : canon14 u = true) : ord4C u = ord4K (pk u) := by
  simp only [ord4C, ord4K, sq14]
  rw [beq_pk (canon14_mul14 _ _) canon14_one14, beq_pk (canon14_mul14 _ _) canon14_one14,
    pkm (canon14_mul14 _ _) (canon14_mul14 _ _), pkm hu hu, bone]

theorem normVC_pk {z w a : List ℕ} (hz : canon14 z = true) (hw : canon14 w = true)
    (ha : canon14 a = true) : normVC z w a = normVK (pk z) (pk w) (pk a) := by
  have hV : ∀ c ∈ [one14, z, w, mul14 z w], canon14 c = true := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact canon14_one14
    · exact hz
    · exact hw
    · exact canon14_mul14 _ _
  simp only [normVC, normVK]
  rw [conjInC_pk hV ha hz, conjInC_pk hV ha hw]
  simp only [List.map_cons, List.map_nil, bone, pkm hz hw]

theorem classStepC_pk {i j u : List ℕ} (hi : canon14 i = true) (hj : canon14 j = true)
    (hu : canon14 u = true) (xw : List ℕ) :
    classStepC i j u xw =
      classStepK (pk i) (pk j) (pk u) (s7Word GA xw) (s7WordInv GA xw) := by
  obtain ⟨hx, px⟩ := word_pk xw
  obtain ⟨hxi, pxi⟩ := wordInv_pk xw
  rw [← px, ← pxi]
  have hz := canon14_mul14 i i
  have hw := canon14_mul14 u u
  have hi' := canon14_mul14 (mul14 (wordC xw) i) (wordInvC xw)
  have hj' := canon14_mul14 (mul14 (wordC xw) j) (wordInvC xw)
  simp only [classStepC, classStepK, sq14]
  have hany : ((spanC i j).any fun a =>
      (spanC (mul14 (mul14 (wordC xw) i) (wordInvC xw))
        (mul14 (mul14 (wordC xw) j) (wordInvC xw))).any fun b =>
        normVC (mul14 i i) (mul14 u u) a && normVC (mul14 i i) (mul14 u u) b &&
          conjInC (spanC (mul14 (mul14 (wordC xw) i) (wordInvC xw))
            (mul14 (mul14 (wordC xw) j) (wordInvC xw))) (mul14 a b) i &&
          conjInC (spanC (mul14 (mul14 (wordC xw) i) (wordInvC xw))
            (mul14 (mul14 (wordC xw) j) (wordInvC xw))) (mul14 a b) j) =
      ((spanK (pk i) (pk j)).any fun A =>
        (spanK (pk (mul14 (mul14 (wordC xw) i) (wordInvC xw)))
          (pk (mul14 (mul14 (wordC xw) j) (wordInvC xw)))).any fun B =>
          normVK (pk (mul14 i i)) (pk (mul14 u u)) A &&
            normVK (pk (mul14 i i)) (pk (mul14 u u)) B &&
            conjInK (spanK (pk (mul14 (mul14 (wordC xw) i) (wordInvC xw)))
              (pk (mul14 (mul14 (wordC xw) j) (wordInvC xw)))) (MUL A B) (pk i) &&
            conjInK (spanK (pk (mul14 (mul14 (wordC xw) i) (wordInvC xw)))
              (pk (mul14 (mul14 (wordC xw) j) (wordInvC xw)))) (MUL A B) (pk j)) := by
    rw [← spanC_map hi hj, List.any_map]
    refine any_congr' fun a ha => ?_
    rw [Function.comp_apply, ← spanC_map hi' hj', List.any_map]
    refine any_congr' fun b hb => ?_
    have ha' := spanC_canon hi hj a ha
    have hb' := spanC_canon hi' hj' b hb
    rw [Function.comp_apply, normVC_pk hz hw ha', normVC_pk hz hw hb',
      conjInC_pk (spanC_canon hi' hj') (canon14_mul14 a b) hi,
      conjInC_pk (spanC_canon hi' hj') (canon14_mul14 a b) hj, spanC_map hi' hj', pkm ha' hb']
  rw [hany, beq_pk (canon14_mul14 _ _) canon14_one14, beq_pk (canon14_mul14 _ _) (canon14_mul14 _ _),
    inSpanC_pk hi' hj' hu, inSpanC_pk hi hj hi', inSpanC_pk hi hj hj', normC_pk hi hj hi',
    normC_pk hi hj hj', bone]
  simp only [pkm (canon14_mul14 _ _) hx, pkm (canon14_mul14 _ _) hxi, pkm hx hi, pkm hx hj,
    pkm hx hxi, pkm hx hz, pkm hw hx, pkm hi hi, pkm hu hu]

theorem classCheckC_pk {i j : List ℕ} (hi : canon14 i = true) (hj : canon14 j = true)
    {S : List (List ℕ)} (hS : ∀ c ∈ S, canon14 c = true) (X : List (List ℕ)) :
    classCheckC i j S X = classCheckK (pk i) (pk j) (S.map pk)
      (X.map fun w => (s7Word GA w, s7WordInv GA w)) := by
  unfold classCheckC classCheckK
  simp only [List.all_map, List.any_map, Function.comp_def]
  refine all_congr' fun u hu => ?_
  rw [ord4C_pk (hS u hu), any_congr' fun xw _ => classStepC_pk hi hj (hS u hu) xw]

theorem normAllC_pk {i j : List ℕ} (hi : canon14 i = true) (hj : canon14 j = true)
    {C : List (List ℕ)} (hC : ∀ c ∈ C, canon14 c = true) :
    normAllC i j C = (C.map pk).all (normK (pk i) (pk j)) := by
  unfold normAllC
  rw [List.all_map]
  exact all_congr' fun c hc => normC_pk hi hj (hC c hc)

theorem q8InCheckC_pk {L : List (List ℕ)} (hL : ∀ c ∈ L, canon14 c = true) {i₁ j₁ i₂ j₂ : List ℕ}
    (hi₁ : canon14 i₁ = true) (hj₁ : canon14 j₁ = true) (hi₂ : canon14 i₂ = true)
    (hj₂ : canon14 j₂ = true) :
    q8InCheckC L i₁ j₁ i₂ j₂ = q8InK (L.map pk) (pk i₁) (pk j₁) (pk i₂) (pk j₂) := by
  have hF : (L.map pk).filter ord4K = (L.filter ord4C).map pk := by
    rw [List.filter_map, List.filter_congr (p := ord4K ∘ pk) (q := ord4C)
      fun c hc => (ord4C_pk (hL c hc)).symm]
  have hF' : ∀ c ∈ L.filter ord4C, canon14 c = true := fun c hc => hL c (List.mem_filter.1 hc).1
  unfold q8InCheckC q8InK
  simp only [hF, List.map_map, List.all_map, Function.comp_def]
  refine all_congr' fun a ha => ?_
  refine all_congr' fun b hb => ?_
  have ha' := hF' a ha
  have hb' := hF' b hb
  simp only [sq14]
  rw [beq_pk (canon14_mul14 _ _) (canon14_mul14 _ _), beq_pk (canon14_mul14 _ _) hb',
    pkm (canon14_mul14 _ _) ha', pkm ha' hb', pkm ha' ha', pkm hb' hb', inSpanC_pk hi₁ hj₁ ha',
    inSpanC_pk hi₁ hj₁ hb', inSpanC_pk hi₂ hj₂ ha', inSpanC_pk hi₂ hj₂ hb']

theorem tab_list {E : Array (List ℕ)} {n : ℕ} {X : ℕ → ℕ} (hsz : E.size = n)
    (hr : ∀ t < n, canon14 (E.getD t []) = true ∧ pk (E.getD t []) = X t) :
    (∀ c ∈ E.toList, canon14 c = true) ∧ E.toList.map pk = (List.range n).map X := by
  refine ⟨fun c hc => ?_, List.ext_getElem (by simp [hsz]) fun t h1 h2 => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hc
    rw [Array.getElem_toList, getElem_getD _ []]
    exact (hr t (by simpa [hsz] using ht)).1
  · have ht : t < n := by simpa [hsz] using h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList,
      getElem_getD _ []]
    exact (hr t ht).2

theorem tS : (∀ c ∈ elemsS.toList, canon14 c = true) ∧
    elemsS.toList.map pk = (List.range 64).map XS :=
  tab_list tabS.1 tabS.2.2.2.2

theorem tX : (∀ c ∈ elemsX.toList, canon14 c = true) ∧
    elemsX.toList.map pk = (List.range 576).map XX :=
  tab_list tabX.1 tabX.2.2.2.2

theorem ok517003 : g23S7Basic () = true ∧ g23S7Class1 () = true ∧ g23S7Class2 () = true ∧
    g23S7Norm () = true ∧ g23S7Q8 () = true := by
  have h := s7517003_ok
  simp only [s7K, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hB, hC1⟩, hC2⟩, hN⟩, hQ⟩ := h
  obtain ⟨c1, p1⟩ := word_pk i1W
  obtain ⟨d1, q1⟩ := word_pk j1W
  obtain ⟨c2, p2⟩ := word_pk i2W
  obtain ⟨d2, q2⟩ := word_pk j2W
  have e1 : i1 = wordC i1W := rfl
  have f1 : j1 = wordC j1W := rfl
  have e2 : i2 = wordC i2W := rfl
  have f2 : j2 = wordC j2W := rfl
  have hCW : conjW.map (fun w => (s7Word GA w, s7WordInv GA w)) = s7CW := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold g23S7Basic
    rw [e1, f1, e2, f2, q8RelC_pk ⟨c1, p1⟩ ⟨d1, q1⟩, q8RelC_pk ⟨c2, p2⟩ ⟨d2, q2⟩, sq14, sq14,
      beq_pk (canon14_mul14 _ _) btc.1, beq_pk (canon14_mul14 _ _) btc.1, pkm c1 c1, pkm c2 c2,
      btc.2, inSpanC_pk c1 d1 c2, p1, q1, p2]
    exact hB
  · unfold g23S7Class1
    rw [e1, f1, classCheckC_pk c1 d1 tS.1, tS.2, p1, q1, hCW]
    exact hC1
  · unfold g23S7Class2
    rw [e2, f2, classCheckC_pk c2 d2 tS.1, tS.2, p2, q2, hCW]
    exact hC2
  · simp only [g23S7Norm]
    rw [e1, f1, e2, f2, normAllC_pk c1 d1 tX.1, normAllC_pk c2 d2 tX.1, normAllC_pk c1 d1 tS.1,
      normAllC_pk c2 d2 tS.1, tX.2, tS.2, p1, q1, p2, q2]
    exact hN
  · unfold g23S7Q8
    rw [e1, f1, e2, f2, q8InCheckC_pk tS.1 c1 d1 c2 d2, tS.2, p1, q1, p2, q2]
    exact hQ

end CFSG.KD.G2Three

end
