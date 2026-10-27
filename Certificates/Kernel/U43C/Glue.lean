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
  exact Finset.sum_congr rfl fun i hi' => if_pos (Finset.mem_range.1 hi')

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

noncomputable def c9575PL : List (ℕ × ℕ) := (List.range 40319).map fun c => (OPP c / 2, OPP c % 2)

noncomputable def c9575C (i : ℕ) : ℕ :=
  if i % 2 = 0 then wC (OW (i / 2))
  else if wP (OW (i / 2)) 0 = wC (OW (i / 2)) then wC (OW (i / 2)) + 1 else wC (OW (i / 2))

noncomputable def c9575POS (i : ℕ) : ℕ := wP (OW (i / 2)) (i % 2)

def c9575SF (i : ℕ) : Prop :=
  i / 2 < c9575C i ∧ c9575POS i ≤ c9575C i ∧ c9575POS i < 40320 ∧
    OX (c9575POS i) = conjF OGA OGB (i % 2) (OX (i / 2)) ∧
    (c9575POS i = c9575C i → OPP (c9575C i - 1) = i ∧ c9575C (i + 1) = c9575C i + 1) ∧
    (c9575POS i ≠ c9575C i → c9575C (i + 1) = c9575C i)

theorem c9575C_even (h : ℕ) : c9575C (2 * h) = wC (OW h) := by
  have e0 : 2 * h % 2 = 0 := by omega
  unfold c9575C
  rw [if_pos e0, Nat.mul_div_cancel_left h (by decide)]

theorem c9575C_odd (h : ℕ) : c9575C (2 * h + 1) =
    if wP (OW h) 0 = wC (OW h) then wC (OW h) + 1 else wC (OW h) := by
  have e : (2 * h + 1) / 2 = h := by omega
  have e1 : ¬(2 * h + 1) % 2 = 0 := by omega
  unfold c9575C
  rw [if_neg e1, e]

theorem c9575POS_eq (h s : ℕ) (hs : s < 2) : c9575POS (2 * h + s) = wP (OW h) s := by
  have e1 : (2 * h + s) / 2 = h := by omega
  have e2 : (2 * h + s) % 2 = s := by omega
  unfold c9575POS
  rw [e1, e2]

theorem c9575_head : ∀ h < 40320, stepF OX OGA OGB OPP 40320 h 0 (wC (OW h)) (wP (OW h) 0) (OX h)
    (fun c1 => stepF OX OGA OGB OPP 40320 h 1 c1 (wP (OW h) 1) (OX h)
      fun c2 => Nat.beq (wC (OW (h + 1))) c2) = true := by
  have chunk : ∀ lo, ostepF OX OGA OGB OW OPP 40320 lo 5040 79 = true → ∀ h, lo ≤ h →
      h < lo + 5040 → stepF OX OGA OGB OPP 40320 h 0 (wC (OW h)) (wP (OW h) 0) (OX h)
        (fun c1 => stepF OX OGA OGB OPP 40320 h 1 c1 (wP (OW h) 1) (OX h)
          fun c2 => Nat.beq (wC (OW (h + 1))) c2) = true := by
    intro lo hc h h1 h2
    have := ostep_at hc (by decide) (h - lo) (by omega)
    rwa [Nat.add_sub_of_le h1] at this
  intro h hh
  by_cases a0 : h < 5040
  · exact chunk 0 c9575Orb0_ok h (by omega) (by omega)
  by_cases a1 : h < 10080
  · exact chunk 5040 c9575Orb1_ok h (by omega) (by omega)
  by_cases a2 : h < 15120
  · exact chunk 10080 c9575Orb2_ok h (by omega) (by omega)
  by_cases a3 : h < 20160
  · exact chunk 15120 c9575Orb3_ok h (by omega) (by omega)
  by_cases a4 : h < 25200
  · exact chunk 20160 c9575Orb4_ok h (by omega) (by omega)
  by_cases a5 : h < 30240
  · exact chunk 25200 c9575Orb5_ok h (by omega) (by omega)
  by_cases a6 : h < 35280
  · exact chunk 30240 c9575Orb6_ok h (by omega) (by omega)
  · exact chunk 35280 c9575Orb7_ok h (by omega) (by omega)

theorem c9575_sf {i : ℕ} (hi : i < 80640) : c9575SF i := by
  obtain ⟨h, s, hs, rfl⟩ : ∃ h s, s < 2 ∧ i = 2 * h + s :=
    ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), (Nat.div_add_mod i 2).symm⟩
  have hh : h < 40320 := by omega
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := stepF_spec (c9575_head h hh)
  have e1' : (2 * h + s) / 2 = h := by omega
  have e2' : (2 * h + s) % 2 = s := by omega
  unfold c9575SF
  rw [e1', e2', c9575POS_eq h s hs]
  interval_cases s
  · rw [Nat.add_zero, c9575C_even, c9575C_odd]
    exact ⟨a1, b1, c1, d1, fun hp => ⟨(e1 hp).1, if_pos hp⟩, fun hp => if_neg hp⟩
  · have hk : stepF OX OGA OGB OPP 40320 h 1 (c9575C (2 * h + 1)) (wP (OW h) 1) (OX h)
        (fun c2 => Nat.beq (wC (OW (h + 1))) c2) = true := by
      rw [c9575C_odd]
      split_ifs with hp
      · exact (e1 hp).2
      · exact f1 hp
    obtain ⟨a2, b2, c2, d2, e2, f2⟩ := stepF_spec hk
    have e3 : 2 * h + 1 + 1 = 2 * (h + 1) := by omega
    rw [e3, c9575C_even]
    refine ⟨a2, b2, c2, d2, fun hp => ⟨(e2 hp).1, ?_⟩, fun hp => ?_⟩
    · exact (Nat.eq_of_beq_eq_true (e2 hp).2)
    · exact (Nat.eq_of_beq_eq_true (f2 hp))

theorem c9575_hit : ∀ n ≤ 80640, ∀ c, 1 ≤ c → c < c9575C n →
    ∃ i < n, c9575C i = c ∧ c9575POS i = c9575C i := by
  have hC0 : c9575C 0 = 1 := by
    have h := c9575OGens_ok
    simp only [Bool.and_eq_true] at h
    have := c9575C_even 0
    rw [Nat.mul_zero] at this
    rw [this]
    exact Nat.eq_of_beq_eq_true h.1.1.2
  intro n
  induction n with
  | zero =>
    intro _ c h1 h2
    omega
  | succ n ih =>
    intro hn c h1 h2
    have hsf := c9575_sf (i := n) (by omega)
    unfold c9575SF at hsf
    obtain ⟨-, -, -, -, e, f⟩ := hsf
    by_cases hc : c < c9575C n
    · obtain ⟨i, hi, hx⟩ := ih (by omega) c h1 hc
      exact ⟨i, by omega, hx⟩
    · by_cases hp : c9575POS n = c9575C n
      · have := (e hp).2
        exact ⟨n, by omega, by omega, hp⟩
      · have := f hp
        omega

theorem uOrbitCheck_kc : uOrbitCheck = true := by
  have hO := c9575OGens_ok
  simp only [Bool.and_eq_true] at hO
  obtain ⟨⟨⟨o1, o2⟩, o3⟩, o4⟩ := hO
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
  have hlen : c9575PL.length = 40319 := by simp [c9575PL]
  have hPL : ∀ j < 40319, c9575PL.getD j (0, 0) = (OPP j / 2, OPP j % 2) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)]
    simp [c9575PL]
  have hfin : c9575C 80640 = 40320 :=
    (c9575C_even 40320).trans (Nat.eq_of_beq_eq_true o3)
  have hpar : ∀ j < c9575PL.length, (c9575PL.getD j (0, 0)).1 ≤ 0 + j ∧
      (c9575PL.getD j (0, 0)).2 < 2 ∧
      OX (0 + j + 1) = conjF OGA OGB (c9575PL.getD j (0, 0)).2 (OX (c9575PL.getD j (0, 0)).1) := by
    intro j hj
    rw [hlen] at hj
    obtain ⟨i, hi, hc, hp⟩ := c9575_hit 80640 le_rfl (j + 1) (by omega) (by rw [hfin]; omega)
    have hsf := c9575_sf hi
    unfold c9575SF at hsf
    obtain ⟨a, -, -, d, e, -⟩ := hsf
    have hopp : OPP j = i := by
      have := (e hp).1
      rwa [hc, Nat.add_sub_cancel] at this
    rw [hPL j hj, hopp, Nat.zero_add]
    dsimp only
    refine ⟨by omega, Nat.mod_lt _ (by decide), ?_⟩
    rw [← hc, ← hp, d]
  have h1 : ∀ x : List ℕ, (#[x] : Array (List ℕ)).getD 0 x = x := fun x => rfl
  have key := orbit_par (x₀ := uAt uB0) hgc c9575PL #[uAt uB0] 0 rfl (fun t ht => by
    have : t = 0 := by omega
    subst this
    rw [h1]
    exact hx0) hpar
  rw [hlen] at key
  set E := orbitBuild (uAt uB0) orbGens c9575PL with hEdef
  have hEs : E.size = 40320 := key.1
  have hE : ∀ t < 40320, DatF (E.getD t []) (OX t) := fun t ht => by
    rw [getD_irrel (by rw [hEs]; exact ht) [] (uAt uB0)]
    exact key.2 t ht
  have hOX := sort_inj c9575OSort_ok (by decide)
  have hd : ∀ t < E.size, ∀ t' < E.size, E.getD t [] = E.getD t' [] → t = t' := by
    intro t ht t' ht' h
    rw [hEs] at ht ht'
    exact hOX t ht t' ht' (by rw [← (hE t ht).2, ← (hE t' ht').2, h])
  have hP : ∀ c, c9575PL.toArray.getD c (0, 0) = c9575PL.getD c (0, 0) := fun c => by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_toArray]
  have hglen : orbGens.length = 2 := rfl
  have hbfs : bfsParents (uAt uB0) (fun x p => conjStep p x) orbGens 40320 = c9575PL := by
    have := bfsParents_replay (one := uAt uB0) (mul := fun x p => conjStep p x) (gens := orbGens)
      (fuel := 40320) (E := E) (P := c9575PL.toArray) (C := c9575C) (POS := c9575POS)
      (fmtF_inj (hE 0 (by decide)).1 hx0.1 (by rw [(hE 0 (by decide)).2, hx0.2]))
      (by rw [hEs]; decide) hd (by rw [List.size_toArray, hlen, hEs])
      (by
        have := c9575C_even 0
        rw [Nat.mul_zero] at this
        rw [this]
        exact Nat.eq_of_beq_eq_true o2)
      (fun h hh s hs => by
        rw [hglen] at hs ⊢
        have hsf := c9575_sf (i := h * 2 + s) (by omega)
        unfold c9575SF at hsf
        obtain ⟨a, b, c, d, e, f⟩ := hsf
        have e1 : (h * 2 + s) / 2 = h := by omega
        have e2 : (h * 2 + s) % 2 = s := by omega
        rw [e1] at a
        rw [e1, e2] at d
        unfold StepOK
        have hR := hgc s (by omega) (hE h hh)
        have hg : orbGens.getD s [] = orbGens.getD s (wordPair []) :=
          listGetD_irrel (by rw [hglen]; exact hs) _ _
        refine ⟨fun _ => ⟨b, by rw [hEs]; exact c, ?_, fun hp => ⟨(e hp).2, ?_⟩,
          fun hp => f (by omega)⟩, fun hn => absurd a hn⟩
        · rw [hg]
          exact fmtF_inj (hE _ c).1 hR.1 (by rw [(hE _ c).2, hR.2, d])
        · rw [hP, hPL _ (by omega), (e hp).1, e1, e2])
      (by rw [hglen, hfin, hEs])
    rw [this, List.toList_toArray]
  unfold uOrbitCheck uOrbit
  rw [hbfs, ← hEdef, hEs, distinctCheck_of hd]
  all_goals rfl

theorem uClassCheck_kc : uClassCheck = true := by
  simp only [uClassCheck, uRtCheck_kc, uKindCheck_kc, uCentCheck_kc, uOrbitCheck_kc, uZCheck_kc,
    Bool.and_self]

end CFSG.KC.U43C

end
