module

public import Certificates.Kernel.U43C.Checks
public import Certificates.Kernel.U43.Final
public import CFSG.Certificates.Kernel.U43.ClassSound

public section

namespace CFSG.KC.U43C

open CFSG.KC.Loop CFSG.KD.U43 CFSG.KD.U43C CFSG.KD.G2Three CFSG.KC.G2Three CFSG.KC.U43
  CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec4.Item434RemU43

theorem c9575_gens : ∀ s < 3, DatF (uGens.getD s one4) (UGF s) := by
  intro s hs
  have e := Nat.eq_of_beq_eq_true (allBelow_g2 c9575Gens_ok (by decide) s hs)
  have hl : s < uGenWords.length := by
    have : uGenWords.length = 3 := rfl
    omega
  have hg : uGens = uGenWords.map wordCode := rfl
  have hw : uGens.getD s one4 = wordCode (uGenWords.getD s []) := by
    rw [hg, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map,
      List.getD_eq_getElem _ _ hl]
  rw [hw, e]
  exact wordDF c9575Letters_ok _

theorem c9575_dat {t : ℕ} (ht : t < 729) : DatF (uAt t) (UXF t) := by
  have hpl : uPar.length = 728 := by decide +kernel
  have key := build_parF (X := UXF) c9575_gens uPar #[one4] 0 rfl (fun t ht => by
    have : t = 0 := by omega
    subst this
    rw [Nat.eq_of_beq_eq_true c9575One_ok]
    exact oneDF) c9575Par_ok
  rw [hpl] at key
  have hs : t < uElems.size := by rw [uTable.1]; exact ht
  unfold uAt
  rw [getD_irrel hs [] one4]
  unfold uElems build
  exact key.2 t (by omega)

theorem c9575_comm {a b : List ℕ} {A B : ℕ} (ha : DatF a A) (hb : DatF b B) :
    commutes4 a b = commF A B :=
  beqDF (mulDF ha hb) (mulDF hb ha)

theorem c9575_cube {a : List ℕ} {A : ℕ} (ha : DatF a A) : (cube4 a == one4) = cubeF A :=
  beqDF (mulDF ha (mulDF ha ha)) oneDF

theorem c9575_pow {a : List ℕ} {A : ℕ} (ha : DatF a A) {k : ℕ} (hk : k < 3) :
    DatF (pow4 a k) (powF A k) := by
  interval_cases k
  · exact oneDF
  · exact ha
  · exact mulDF ha ha

theorem c9575_data : (uLiftBasis.length == 4) = true ∧ uLiftBasis.all (· < 729) = true ∧
    (uRt.length == 81) = true ∧ uRt.all (· < 729) = true ∧ (uKind.length == 729) = true ∧
    decide (uB0 < 729) = true ∧ decide (uZ < 729) = true ∧
    (uConvR.all fun e => wordOK e.2) = true := by
  have h := c9575Data_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, k⟩ := h
  exact ⟨a, b, c, d, e, f, g, k⟩

theorem c9575_memF {p : ℕ} : ∀ {l : List ℕ}, memF p l = true → l.contains p = true
  | [], h => absurd h Bool.false_ne_true
  | a :: l, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (memF p l) true (Nat.beq a p) = true := h
    cases hq : Nat.beq a p
    · rw [hq] at h'
      have hm : p ∈ l := by simpa using c9575_memF (l := l) h'
      simp [hm]
    · rw [Nat.eq_of_beq_eq_true hq]
      simp

theorem c9575_basis (a : ℕ) (ha : a < 4) : DatF (uAt (uLiftBasis.getD a 0)) (basF UXF a) :=
  c9575_dat (by interval_cases a <;> decide)

theorem c9575_rtProd (e : ℕ) : DatF (rtProd e) (rtF (basF UXF) e) := by
  unfold rtProd rtF
  exact mulDF (mulDF (mulDF (c9575_pow (c9575_basis 0 (by decide)) (Nat.mod_lt _ (by decide)))
    (c9575_pow (c9575_basis 1 (by decide)) (Nat.mod_lt _ (by decide))))
    (c9575_pow (c9575_basis 2 (by decide)) (Nat.mod_lt _ (by decide))))
    (c9575_pow (c9575_basis 3 (by decide)) (Nat.mod_lt _ (by decide)))

theorem c9575_rt_at {e : ℕ} (he : e < 81) :
    RTP e < 729 ∧ uRt.contains (RTP e) = true ∧ RTI (RTP e) = e ∧ rtProd e = uAt (RTP e) := by
  have hrt := c9575Rt_ok
  unfold rtK at hrt
  simp only [Bool.and_eq_true] at hrt
  have h := allBelow_g2 hrt.2 (by decide) e he
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hr := c9575_dat h1
  exact ⟨h1, c9575_memF h2, h3,
    fmtF_inj (c9575_rtProd e).1 hr.1 (by rw [(c9575_rtProd e).2, hr.2, h4])⟩

theorem uRtCheck_kc : uRtCheck = true := by
  have hrt := c9575Rt_ok
  unfold rtK at hrt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨hc, hq⟩, -⟩ := hrt
  obtain ⟨d1, d2, d3, d4, -⟩ := c9575_data
  have hes : ∀ t < 81, ((List.range 81).map rtProd).toArray.getD t [] = rtProd t := by
    intro t ht
    simp [Array.getD_eq_getD_getElem?, ht]
  unfold uRtCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨d1, d2⟩, all_range_of fun a ha => all_range_of fun b hb => ?_⟩,
    all_range_of fun a ha => ?_⟩, d3⟩, d4⟩, all_range_of fun e he => ?_⟩,
    distinctCheck_of fun t ht t' ht' h => ?_⟩
  · rw [c9575_comm (c9575_basis a ha) (c9575_basis b hb)]
    exact allBelow_g2 (allBelow_g2 hc (by decide) a ha) (by decide) b hb
  · rw [c9575_cube (c9575_basis a ha)]
    exact allBelow_g2 hq (by decide) a ha
  · obtain ⟨h1, h2, -, h4⟩ := c9575_rt_at he
    rw [h4, posOf_at h1]
    exact h2
  · have hs : ((List.range 81).map rtProd).toArray.size = 81 := by simp
    rw [hs] at ht ht'
    rw [hes t ht, hes t' ht'] at h
    obtain ⟨a1, -, a3, a4⟩ := c9575_rt_at ht
    obtain ⟨b1, -, b3, b4⟩ := c9575_rt_at ht'
    rw [a4, b4] at h
    have e : RTP t = RTP t' := by rw [← posOf_at a1, ← posOf_at b1, h]
    rw [← a3, ← b3, e]

theorem c9575_kindF {X A : ℕ → ℕ} {b : ℕ} : ∀ (ks : List ℕ) (p : ℕ), kindF X A b ks p = true →
    ∀ j < ks.length, ks.getD j 0 = 3 →
      wordOK (convDWord (p + j)) = true ∧ wconjF A (convDWord (p + j)) (X (p + j)) = b
  | [], _, _, j, hj, _ => absurd hj (Nat.not_lt_zero j)
  | k :: ks, p, h, j, hj, hk => by
    have h' : Bool.rec (motive := fun _ => Bool) false (kindF X A b ks (p + 1))
        (Bool.rec (motive := fun _ => Bool) true
          (wordOK (convDWord p) && Nat.beq (wconjF A (convDWord p) (X p)) b) (Nat.beq k 3)) =
        true := h
    obtain ⟨h1, h2⟩ := bAnd_g2 h'
    cases j with
    | zero =>
      rw [List.getD_cons_zero] at hk
      have h1' : (wordOK (convDWord p) && Nat.beq (wconjF A (convDWord p) (X p)) b) = true := by
        rw [hk] at h1
        exact h1
      rw [Bool.and_eq_true] at h1'
      exact ⟨h1'.1, Nat.eq_of_beq_eq_true h1'.2⟩
    | succ j =>
      rw [List.getD_cons_succ] at hk
      have := c9575_kindF ks (p + 1) h2 j (by simp at hj; omega) hk
      rw [Nat.add_assoc, Nat.add_comm 1 j] at this
      exact this

theorem uKindCheck_kc : uKindCheck = true := by
  obtain ⟨-, -, -, -, d5, d6, -, d8⟩ := c9575_data
  have hk := c9575_kindF uKind 0 c9575Kind_ok
  have hl : uKind.length = 729 := by simpa using d5
  have hb : uB0 < 729 := by simpa using d6
  unfold uKindCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨d5, d6⟩, all_range_of fun p hp => ?_⟩, d8⟩
  unfold kindOK
  rw [Bool.or_eq_true]
  by_cases h3 : uKind.getD p 0 = 3
  · right
    obtain ⟨w, e⟩ := hk p (by omega) h3
    rw [Nat.zero_add] at w e
    rw [Bool.and_eq_true, beqDF (conjDF c9575Letters_ok _ (c9575_dat hp)) (c9575_dat hb)]
    refine ⟨w, ?_⟩
    rw [Nat.beq_eq]
    exact e
  · left
    simpa using h3

theorem uZCheck_kc : uZCheck = true := by
  obtain ⟨-, -, -, -, -, -, d7, -⟩ := c9575_data
  have hz : uZ < 729 := by simpa using d7
  have h := c9575Z_ok
  unfold zF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold uZCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨d7, ?_⟩, ?_⟩, all_range_of fun q hq => ?_⟩
  · rw [beqDF (c9575_dat hz) oneDF]
    exact h1
  · rw [c9575_cube (c9575_dat hz)]
    exact h2
  · rw [c9575_comm (c9575_dat hq) (c9575_dat hz)]
    exact allBelow_g2 h3 (by decide) q hq

private theorem c9575_sumBelow_eq (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have sel : ∀ (b : Bool) (x : ℕ), Bool.rec (motive := fun _ => ℕ) 0 x b =
      if b = true then x else 0 := by
    intro b x
    cases b <;> rfl
  have hgen : ∀ h, sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        have p : (2 : ℕ) ^ 6 = 64 := rfl
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, p]
        omega
      simp only [e, sel, Nat.blt_eq]
  rw [hgen hi, (Nat.add_sub_of_le hm).symm, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi' => ite_eq_left (Finset.mem_range.1 hi')

private theorem c9575_count (p : ℕ → Bool) : ∀ n,
    ∑ i ∈ Finset.range n, Bool.rec (motive := fun _ => ℕ) 0 1 (p i) =
      ((List.range n).filter p).length
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, c9575_count p n, List.range_succ, List.filter_append,
      List.length_append]
    cases h : p n <;> simp [h]

private theorem c9575_card {n hi a b : ℕ} (K : ℕ → ℕ → Bool) (S : ℕ → ℕ) (Y : ℕ)
    (hm : n ≤ 64 * hi) (ha : a = 1) (hb : b = 0) :
    sumBelow n hi (fun i => Bool.rec (motive := fun _ => ℕ) b a (K (S i) Y)) =
      ((List.range n).filter fun i => K (S i) Y).length := by
  subst ha hb
  exact (c9575_sumBelow_eq n hi _ hm).trans (c9575_count _ n)

theorem uCentCheck_kc : uCentCheck = true := by
  obtain ⟨-, -, -, -, -, d6, -, -⟩ := c9575_data
  have hb : uB0 < 729 := by simpa using d6
  have h := c9575Cent_ok
  unfold centF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hn : centN UXF (UXF uB0) = 81 := Nat.eq_of_beq_eq_true h2
  have hc : centN UXF (UXF uB0) =
      ((List.range 729).filter fun q => commF (UXF q) (UXF uB0)).length :=
    c9575_card commF UXF (UXF uB0) (by decide) rfl rfl
  have hf : ((List.range 729).filter fun q => commutes4 (uAt q) (uAt uB0)) =
      (List.range 729).filter fun q => commF (UXF q) (UXF uB0) :=
    List.filter_congr fun q hq => c9575_comm (c9575_dat (List.mem_range.1 hq)) (c9575_dat hb)
  unfold uCentCheck
  rw [Bool.and_eq_true, c9575_cube (c9575_dat hb), hf, ← hc, hn]
  exact ⟨h1, rfl⟩

theorem c9575_par {j : ℕ} (hj : j < 40319) :
    (uOrbPar.getD j (0, 0)).1 ≤ j ∧ (uOrbPar.getD j (0, 0)).2 < 2 ∧
      OX (j + 1) = conjF OGA OGB (uOrbPar.getD j (0, 0)).2 (OX (uOrbPar.getD j (0, 0)).1) := by
  have hlen : uOrbParW.length = 630 := by decide +kernel
  have hg : uOrbPar.getD j (0, 0) =
      (Nat.land (Nat.shiftRight (uOrbParW.getD (j / 64) 0) (17 * (j % 64))) 131071 / 2,
        Nat.land (Nat.shiftRight (uOrbParW.getD (j / 64) 0) (17 * (j % 64))) 131071 % 2) := by
    simp only [uOrbPar, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
      Option.map_some, Option.getD_some]
  have chunk : ∀ lo, oparF OX OGA OGB 40319 ((uOrbParW.drop lo).take 79) lo = true →
      lo ≤ j / 64 → j / 64 < lo + 79 →
      (uOrbPar.getD j (0, 0)).1 ≤ j ∧ (uOrbPar.getD j (0, 0)).2 < 2 ∧
        OX (j + 1) = conjF OGA OGB (uOrbPar.getD j (0, 0)).2 (OX (uOrbPar.getD j (0, 0)).1) := by
    intro lo hc h1 h2
    have hi : j / 64 - lo < ((uOrbParW.drop lo).take 79).length := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    have := oparF_at _ lo hc (j / 64 - lo) hi (j % 64) (Nat.mod_lt _ (by decide)) (by omega)
    have e : 64 * (lo + (j / 64 - lo)) + j % 64 = j := by omega
    have hw : ((uOrbParW.drop lo).take 79).getD (j / 64 - lo) 0 = uOrbParW.getD (j / 64) 0 := by
      have e2 : lo + (j / 64 - lo) = j / 64 := by omega
      have h79 : j / 64 - lo < 79 := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, e2, h79,
        ite_true]
    rw [e, hw] at this
    rw [hg]
    exact ⟨this.1, Nat.mod_lt _ (by decide), this.2⟩
  have hq : j / 64 < 630 := by omega
  by_cases a0 : j / 64 < 79
  · exact chunk 0 c9575OPar0_ok (by omega) (by omega)
  by_cases a1 : j / 64 < 158
  · exact chunk 79 c9575OPar1_ok (by omega) (by omega)
  by_cases a2 : j / 64 < 237
  · exact chunk 158 c9575OPar2_ok (by omega) (by omega)
  by_cases a3 : j / 64 < 316
  · exact chunk 237 c9575OPar3_ok (by omega) (by omega)
  by_cases a4 : j / 64 < 395
  · exact chunk 316 c9575OPar4_ok (by omega) (by omega)
  by_cases a5 : j / 64 < 474
  · exact chunk 395 c9575OPar5_ok (by omega) (by omega)
  by_cases a6 : j / 64 < 553
  · exact chunk 474 c9575OPar6_ok (by omega) (by omega)
  · exact chunk 553 c9575OPar7_ok (by omega) (by omega)

theorem uOrbitCheck_kc : uOrbitCheck = true := by
  have hO := c9575OGens_ok
  simp only [Bool.and_eq_true] at hO
  obtain ⟨o1, o4⟩ := hO
  have hga : ∀ s < 2, OGA s = wordF UAF [s] := fun s hs => by
    have := allBelow_g2 o4 (by decide) s hs
    simp only [Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.1
  have hgb : ∀ s < 2, OGB s = wordF UAF (invWord [s]) := fun s hs => by
    have := allBelow_g2 o4 (by decide) s hs
    simp only [Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.2
  have hgc : ∀ s < 2, ∀ {x : List ℕ} {Y : ℕ}, DatF x Y →
      DatF (conjStep (orbGens.getD s (wordPair [])) x) (conjF OGA OGB s Y) :=
    fun s hs _ _ hx => orbGens_conjF c9575Letters_ok hga hgb hs hx
  have hb0 : uB0 < 729 := by decide
  have hx0 : DatF (uAt uB0) (OX 0) := by
    rw [Nat.eq_of_beq_eq_true o1]
    exact c9575_dat hb0
  have hlen : uOrbPar.length = 40319 := by
    simp only [uOrbPar, List.length_map, List.length_range]
  have hpar : ∀ j < uOrbPar.length, (uOrbPar.getD j (0, 0)).1 ≤ 0 + j ∧
      (uOrbPar.getD j (0, 0)).2 < 2 ∧
      OX (0 + j + 1) = conjF OGA OGB (uOrbPar.getD j (0, 0)).2 (OX (uOrbPar.getD j (0, 0)).1) := by
    intro j hj
    rw [hlen] at hj
    rw [Nat.zero_add]
    exact c9575_par hj
  have h1 : ∀ x : List ℕ, (#[x] : Array (List ℕ)).getD 0 x = x := fun x => rfl
  have key := orbit_par (x₀ := uAt uB0) hgc uOrbPar #[uAt uB0] 0 rfl (fun t ht => by
    have : t = 0 := by omega
    subst this
    rw [h1]
    exact hx0) hpar
  rw [hlen] at key
  set E := orbitBuild (uAt uB0) orbGens uOrbPar with hEdef
  have hEs : E.size = 40320 := key.1
  have hE : ∀ t < 40320, DatF (E.getD t []) (OX t) := fun t ht => by
    rw [getD_irrel (by rw [hEs]; exact ht) [] (uAt uB0)]
    exact key.2 t ht
  have hOX := sort_inj c9575OSort_ok (by decide)
  have hd : ∀ t < E.size, ∀ t' < E.size, E.getD t [] = E.getD t' [] → t = t' := by
    intro t ht t' ht' h
    rw [hEs] at ht ht'
    exact hOX t ht t' ht' (by rw [← (hE t ht).2, ← (hE t' ht').2, h])
  unfold uOrbitCheck uOrbit
  rw [← hEdef, hEs, distinctCheck_of hd]
  all_goals rfl

theorem uClassCheck_kc : uClassCheck = true := by
  simp only [uClassCheck, uRtCheck_kc, uKindCheck_kc, uCentCheck_kc, uOrbitCheck_kc, uZCheck_kc,
    Bool.and_self]

end CFSG.KC.U43C

end
