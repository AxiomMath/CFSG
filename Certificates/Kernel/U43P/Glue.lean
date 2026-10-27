module

public import Certificates.Kernel.U43P.Checks
public import Certificates.Kernel.U43C.Glue
public import CFSG.Certificates.Kernel.U43.PairSound

public section

namespace CFSG.KC.U43P

open CFSG.KC.Loop CFSG.KD.U43 CFSG.KD.U43C CFSG.KD.U43P CFSG.KD.G2Three CFSG.KC.G2Three
  CFSG.KC.U43 CFSG.KC.U43C CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec4.Item434RemU43

theorem c9576_tab : TabF UXF := ⟨fun _ ht => c9575_dat ht, fun _ ht => posOf_at ht⟩

theorem c9576_sq : ∀ t < 729, SQP t = MF (UXF t) (UXF t) := fun t ht =>
  Nat.eq_of_beq_eq_true (allBelow_g2 c9576Sq_ok (by decide) t ht)

theorem c9576_knd : ∀ q < 729, KND q = uKind.getD q 0 := fun q hq => by
  have hl : uKind.length = 729 := by decide +kernel
  have := listF_at KND uKind 0 c9576Knd_ok q (by omega)
  rwa [Nat.zero_add] at this

theorem c9576_o3 {p : ℕ} (hp : p < 729) : isOrd3Arr.getD p false = o3F (UXF p) (SQP p) := by
  have hd := c9575_dat hp
  have e : isOrd3Arr.getD p false = isOrd3 p := by
    unfold isOrd3Arr
    simp [Array.getD, hp]
  rw [e]
  unfold isOrd3 o3F cube4 sq4
  rw [beqDF hd oneDF, beqDF (mulDF hd (mulDF hd hd)) oneDF, c9576_sq p hp]

theorem c9576_ol {t : ℕ} (ht : t < 729) (h : o3F (UXF t) (SQP t) = true) :
    OLI t < 296 ∧ OL (OLI t) = t := by
  have hc := allBelow_g2 c9576Ol_ok (by decide) t ht
  simp only [h] at hc
  change (Nat.blt (OLI t) 296 && Nat.beq (OL (OLI t)) t) = true at hc
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
  exact hc

theorem c9576_rows {lo m : ℕ} (hm : m ≤ 64)
    (h : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) lo m = true) :
    ∀ j < m, ∀ j₂ < 296, bIf(Nat.blt (OL (lo + j)) (OL j₂),
      bIf(commF (UXF (OL (lo + j))) (UXF (OL j₂)),
        ppF UXF SQP KND CAP CBP (UXF uZ) (SQP uZ) (OL (lo + j)) (OL j₂)
          (WP (296 * (lo + j) + j₂)) &&
        cvF UXF SQP CAP CBP (OL (lo + j)) (OL j₂) (WC (296 * (lo + j) + j₂)), true), true) =
      true := by
  intro j hj j₂ hj₂
  have h1 := allBelow_g2 h (by omega) j hj
  simp only [letB_eq] at h1
  exact allBelow_g2 h1 (by decide) j₂ hj₂

theorem c9576_pair {j₁ j₂ : ℕ} (h₁ : j₁ < 296) (h₂ : j₂ < 296) :
    bIf(Nat.blt (OL j₁) (OL j₂), bIf(commF (UXF (OL j₁)) (UXF (OL j₂)),
      ppF UXF SQP KND CAP CBP (UXF uZ) (SQP uZ) (OL j₁) (OL j₂) (WP (296 * j₁ + j₂)) &&
      cvF UXF SQP CAP CBP (OL j₁) (OL j₂) (WC (296 * j₁ + j₂)), true), true) = true := by
  have e : j₁ = 37 * (j₁ / 37) + j₁ % 37 := by omega
  have hr : j₁ % 37 < 37 := Nat.mod_lt _ (by decide)
  have hc : j₁ / 37 < 8 := by omega
  rw [e]
  interval_cases hq : j₁ / 37
  · exact c9576_rows (by decide) c9576Pairs0_ok _ hr _ h₂
  · exact c9576_rows (by decide) c9576Pairs1_ok _ hr _ h₂
  · exact c9576_rows (by decide) c9576Pairs2_ok _ hr _ h₂
  · exact c9576_rows (by decide) c9576Pairs3_ok _ hr _ h₂
  · exact c9576_rows (by decide) c9576Pairs4_ok _ hr _ h₂
  · exact c9576_rows (by decide) c9576Pairs5_ok _ hr _ h₂
  · exact c9576_rows (by decide) c9576Pairs6_ok _ hr _ h₂
  · exact c9576_rows (by decide) c9576Pairs7_ok _ hr _ h₂

theorem c9576_wit {ia ib : ℕ} (hia : ia < 729) (hib : ib < 729) (hlt : ia < ib)
    (ha : o3F (UXF ia) (SQP ia) = true) (hb : o3F (UXF ib) (SQP ib) = true)
    (hc : commF (UXF ia) (UXF ib) = true) : ∃ w v,
      ppF UXF SQP KND CAP CBP (UXF uZ) (SQP uZ) ia ib w = true ∧
      cvF UXF SQP CAP CBP ia ib v = true := by
  obtain ⟨l₁, e₁⟩ := c9576_ol hia ha
  obtain ⟨l₂, e₂⟩ := c9576_ol hib hb
  have h := c9576_pair l₁ l₂
  rw [e₁, e₂, Nat.blt_eq.mpr hlt, hc] at h
  change (ppF UXF SQP KND CAP CBP (UXF uZ) (SQP uZ) ia ib (WP (296 * OLI ia + OLI ib)) &&
    cvF UXF SQP CAP CBP ia ib (WC (296 * OLI ia + OLI ib))) = true at h
  rw [Bool.and_eq_true] at h
  exact ⟨_, _, h.1, h.2⟩

theorem uPairCheck_kc : uPairCheck = true := by
  unfold uPairCheck
  refine all_range_of fun ia hia => ?_
  unfold pairRow
  refine all_range_of fun ib hib => ?_
  by_cases hle : ib ≤ ia
  · simp [hle]
  rw [decide_eq_false hle, Bool.false_or]
  unfold pairOK
  have hda := c9575_dat hia
  have hdb := c9575_dat hib
  rw [c9576_o3 hia, c9576_o3 hib, commF_eq hda hdb]
  cases ha : o3F (UXF ia) (SQP ia)
  · rfl
  cases hb : o3F (UXF ib) (SQP ib)
  · rfl
  cases hc : commF (UXF ia) (UXF ib)
  · rfl
  obtain ⟨w, -, hw, -⟩ := c9576_wit hia hib (by omega) ha hb hc
  rw [ppF_sound c9576_tab c9575Letters_ok c9576Conv_ok c9576_sq c9576_knd hia hib hw]
  rfl

theorem uCoverCheck_kc : uCoverCheck = true := by
  unfold uCoverCheck
  refine all_range_of fun ia hia => ?_
  unfold coverRow
  refine all_range_of fun ib hib => ?_
  by_cases hle : ib ≤ ia
  · simp [hle]
  rw [decide_eq_false hle, Bool.false_or]
  unfold coverOK
  have hda := c9575_dat hia
  have hdb := c9575_dat hib
  rw [c9576_o3 hia, c9576_o3 hib, commF_eq hda hdb]
  cases ha : o3F (UXF ia) (SQP ia)
  · rfl
  cases hb : o3F (UXF ib) (SQP ib)
  · rfl
  cases hc : commF (UXF ia) (UXF ib)
  · rfl
  obtain ⟨-, v, -, hv⟩ := c9576_wit hia hib (by omega) ha hb hc
  have := cvF_sound c9576_tab c9575Letters_ok c9576Conv_ok c9576_sq hia hib hv
  simp only [Bool.not_true, Bool.false_or, Bool.or_assoc] at this ⊢
  exact this

theorem c9577_tri {n i : ℕ} (hn : n < 13) (hi : i < 3) : (yTriple n).getD i 0 < 729 := by
  have hd := c9577Data_ok
  simp only [Bool.and_eq_true] at hd
  have h := (List.all_eq_true.1 hd.1.1.1.1.1.1.2) n (List.mem_range.2 hn)
  simp only [Bool.and_eq_true] at h
  exact tri_lt h.1.1 h.1.2 hi

theorem yEls_getD (n : ℕ) {e : ℕ} (he : e < 27) : (yEls n).getD e [] =
    mul4 (mul4 ([one4, uAt ((yTriple n).getD 0 0), sq4 (uAt ((yTriple n).getD 0 0))].getD (e / 9) [])
      ([one4, uAt ((yTriple n).getD 1 0), sq4 (uAt ((yTriple n).getD 1 0))].getD (e / 3 % 3) []))
      ([one4, uAt ((yTriple n).getD 2 0), sq4 (uAt ((yTriple n).getD 2 0))].getD (e % 3) []) := by
  unfold yEls
  interval_cases e <;> simp

theorem yEls_length (n : ℕ) : (yEls n).length = 27 := by
  unfold yEls
  simp

theorem c9577_sqd {t : ℕ} (ht : t < 729) : DatF (sq4 (uAt t)) (SQP t) := by
  rw [c9576_sq t ht]
  exact mulDF (c9575_dat ht) (c9575_dat ht)

theorem c9577_el {n : ℕ} (hn : n < 13) {e : ℕ} (he : e < 27) :
    DatF ((yEls n).getD e []) (yElF UXF SQP ((yTriple n).getD 0 0) ((yTriple n).getD 1 0)
      ((yTriple n).getD 2 0) e) := by
  rw [yEls_getD n he]
  have t0 := c9577_tri hn (i := 0) (by decide)
  have t1 := c9577_tri hn (i := 1) (by decide)
  have t2 := c9577_tri hn (i := 2) (by decide)
  exact mulDF (mulDF (pw_dat (c9575_dat t0) (c9577_sqd t0) (by omega))
    (pw_dat (c9575_dat t1) (c9577_sqd t1) (by omega)))
    (pw_dat (c9575_dat t2) (c9577_sqd t2) (by omega))

theorem distF_nodup : ∀ l : List ℕ, distF l = true → l.Nodup
  | [] => fun _ => List.nodup_nil
  | a :: t => fun h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (distF t) (!memF a t) = true := h
    obtain ⟨h1, h2⟩ := bAnd_g2 h'
    rw [memF_eq] at h1
    refine List.nodup_cons.2 ⟨fun hm => ?_, distF_nodup t h2⟩
    rw [← List.contains_iff_mem] at hm
    rw [hm] at h1
    exact absurd h1 (by decide)

theorem c9577_yOK {n : ℕ} (hn : n < 13) : yOK n = true := by
  have hd := c9577Data_ok
  simp only [Bool.and_eq_true] at hd
  have hdn := (List.all_eq_true.1 hd.1.1.1.1.1.1.2) n (List.mem_range.2 hn)
  simp only [Bool.and_eq_true] at hdn
  obtain ⟨⟨hl, hlt⟩, hw⟩ := hdn
  have hy := allBelow_g2 c9577Y_ok (by decide) n hn
  unfold yF at hy
  simp only [letB_eq, Bool.and_eq_true] at hy
  obtain ⟨⟨⟨hcm, hcu⟩, hds⟩, hr⟩ := hy
  have hcm' := allBelow_g2 hcm (by decide)
  have hcu' := allBelow_g2 hcu (by decide)
  have hr' := allBelow_g2 hr (by decide)
  have hD : ∀ i < 3, DatF (uAt ((yTriple n).getD i 0)) (UXF ((yTriple n).getD i 0)) :=
    fun i hi => c9575_dat (c9577_tri hn hi)
  unfold yOK
  rw [hl, hlt, hw]
  simp only [Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨⟨all_range_of fun i hi => all_range_of fun j hj => ?_,
    all_range_of fun i hi => ?_⟩, ?_⟩, ?_⟩
  · rw [commF_eq (hD i hi) (hD j hj)]
    exact allBelow_g2 (hcm' i hi) (by decide) j hj
  · have hc := hcu' i hi
    unfold cube4
    rw [beqDF (mulDF (hD i hi) (c9577_sqd (c9577_tri hn hi))) oneDF]
    exact hc
  · have hnd := distF_nodup _ hds
    refine distinctCheck_of fun t ht t' ht' h => ?_
    rw [List.size_toArray, yEls_length] at ht ht'
    have a := c9577_el hn ht
    have b := c9577_el hn ht'
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_toArray, ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD] at h
    have e : yElF UXF SQP ((yTriple n).getD 0 0) ((yTriple n).getD 1 0) ((yTriple n).getD 2 0) t =
        yElF UXF SQP ((yTriple n).getD 0 0) ((yTriple n).getD 1 0) ((yTriple n).getD 2 0) t' := by
      rw [← a.2, ← b.2, h]
    have hm : ((List.range 27).map (yElF UXF SQP ((yTriple n).getD 0 0) ((yTriple n).getD 1 0)
        ((yTriple n).getD 2 0)))[t]'(by simpa using ht) =
        ((List.range 27).map (yElF UXF SQP ((yTriple n).getD 0 0) ((yTriple n).getD 1 0)
        ((yTriple n).getD 2 0)))[t']'(by simpa using ht') := by
      simpa using e
    exact (List.Nodup.getElem_inj_iff hnd).1 hm
  · rw [List.all_eq_true]
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    have hl3 : (yTriple n).length = 3 := by simpa using hl
    have hi3 : i < 3 := by omega
    have hc := hr' i hi3
    simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hc
    obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hc
    rw [← List.getD_eq_getElem _ 0 hi]
    have hcj := conjDF c9575Letters_ok (yWord n) (hD i hi3)
    rw [(pos_of c9576_tab hcj hr1 hr3).2, inRt_eq hr1]
    exact hr2

theorem uYCheck_kc : uYCheck = true := by
  have hd := c9577Data_ok
  simp only [Bool.and_eq_true] at hd
  unfold uYCheck
  rw [hd.1.1.1.1.1.1.1, Bool.true_and]
  exact all_range_of fun n hn => c9577_yOK hn

theorem uLiftCheck_kc : uLiftCheck = true := by
  have hd := c9577Data_ok
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, h1⟩, -⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hd
  have hl := allBelow_g2 c9577Lift_ok (by decide)
  have hB : ∀ i < 4, DatF (liftEl i) (liftF UXF i) := fun i hi =>
    c9575_dat (by interval_cases i <;> decide)
  have hM : ∀ j < 2, ∀ k < 4, ∀ i < 4, liftMat j k i < 3 := fun j hj k hk i hi => by
    have a := List.all_eq_true.1 h6 j (List.mem_range.2 hj)
    have b := List.all_eq_true.1 a k (List.mem_range.2 hk)
    have c := List.all_eq_true.1 b i (List.mem_range.2 hi)
    simpa using c
  unfold uLiftCheck
  rw [h1, h3, h4, h5, h6]
  simp only [Bool.true_and]
  refine all_range_of fun j hj => all_range_of fun i hi => ?_
  have hc := allBelow_g2 (hl j hj) (by decide) i hi
  have hcj := conjDF c9575Letters_ok (uLiftG.getD j []) (hB i hi)
  have hr : DatF (liftRhs j i) (liftRhsF UXF j i) :=
    mulDF (c9575_pow (hB 0 (by decide)) (hM j hj 0 (by decide) i hi))
      (mulDF (c9575_pow (hB 1 (by decide)) (hM j hj 1 (by decide) i hi))
        (mulDF (c9575_pow (hB 2 (by decide)) (hM j hj 2 (by decide) i hi))
          (mulDF (c9575_pow (hB 3 (by decide)) (hM j hj 3 (by decide) i hi)) oneDF)))
  rw [beqDF hcj hr]
  exact hc

end CFSG.KC.U43P

end
