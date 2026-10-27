module

public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDenseP.Axis.Pairs

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC.KDenseP.Axis CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.B.Short
  CFSG.Monster.Griess

@[expose] def TagEq (x : (List Native.Gen × List Native.Gen) × ℕ) : Prop :=
  wordLin x.1.1 (wv x.2) = wordLin x.1.2 (wv x.2)

theorem tagEq_append {A B : List ((List Native.Gen × List Native.Gen) × ℕ)}
    (h : ∀ x ∈ A ++ B, TagEq x) : (∀ x ∈ A, TagEq x) ∧ ∀ x ∈ B, TagEq x :=
  ⟨fun x hx => h x (List.mem_append_left _ hx), fun x hx => h x (List.mem_append_right _ hx)⟩

theorem notTau_of_all {w : List Native.Gen} (h : (w.all fun g => !HS.isTauB g) = true) :
    ∀ g ∈ w, g ≠ Native.Gen.tau := fun g hg e => by
  have := List.all_eq_true.1 h g hg
  subst e
  simp [HS.isTauB] at this

theorem wordLin_append_apply (u v : List Native.Gen) (x : SpaceB) :
    wordLin (u ++ v) x = wordLin v (wordLin u x) := by
  rw [wordLin_append, LinearEquiv.mul_apply]

@[expose] noncomputable def recTag (l : List (Fin 12 × ℕ × ℕ)) :
    List ((List Native.Gen × List Native.Gen) × ℕ) :=
  l.flatMap fun s => (List.range' s.2.1 (s.2.2 - s.2.1)).flatMap fun r =>
    [true, false].flatMap fun ε =>
      [((Cert.gammaW s.1 ++ HS.xW s.1 r ε, Cert.gammaW (Cert.tFin s.1 r ε)), 0),
       ((Cert.gammaW s.1 ++ HS.xW s.1 r ε,
         HS.babyW (HS.bbL s.1 r ε) ++ HS.hppL s.1 r ε ++ Cert.gammaW (Cert.tFin s.1 r ε)), 1),
       ((HS.hppL s.1 r ε, []), 0)]

theorem recTag_fst (l : List (Fin 12 × ℕ × ℕ)) : (recTag l).map Prod.fst = recPairs l := by
  simp [recTag, recPairs, List.map_flatMap]

@[expose] def recBB (l : List (Fin 12 × ℕ × ℕ)) : Bool :=
  l.all fun s => (List.range' s.2.1 (s.2.2 - s.2.1)).all fun r =>
    [true, false].all fun ε => Nat.blt (HS.bbL s.1 r ε) 10

theorem rec_body {l : List (Fin 12 × ℕ × ℕ)} (h : ∀ x ∈ recTag l, TagEq x)
    (hb : recBB l = true) :
    ∀ s ∈ l, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, HS.RecSpec s.1 r ε := by
  intro s hs r h1 h2 ε
  have hr : r ∈ List.range' s.2.1 (s.2.2 - s.2.1) := HS.mem_range'_iff.2 ⟨h1, h2⟩
  have hm : ∀ y, y ∈ [((Cert.gammaW s.1 ++ HS.xW s.1 r ε, Cert.gammaW (Cert.tFin s.1 r ε)), 0),
       ((Cert.gammaW s.1 ++ HS.xW s.1 r ε,
         HS.babyW (HS.bbL s.1 r ε) ++ HS.hppL s.1 r ε ++ Cert.gammaW (Cert.tFin s.1 r ε)), 1),
       ((HS.hppL s.1 r ε, []), 0)] → y ∈ recTag l := fun y hy =>
    List.mem_flatMap.2 ⟨s, hs, List.mem_flatMap.2 ⟨r, hr,
      List.mem_flatMap.2 ⟨ε, HS.mem_bool ε, hy⟩⟩⟩
  have e1 : TagEq _ := h _ (hm _ List.mem_cons_self)
  have e2 : TagEq _ := h _ (hm _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have e3 : TagEq _ := h _ (hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self)))
  have hb' : HS.bbL s.1 r ε < 10 := by
    have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hb s hs) r hr) ε
      (HS.mem_bool ε)
    exact Nat.le_of_ble_eq_true this
  unfold TagEq at e1 e2 e3
  rw [wv_zero, wordLin_append_apply] at e1
  rw [wv_one, wordLin_append_apply, List.append_assoc, wordLin_append_apply] at e2
  rw [wv_zero, wordLin_nil] at e3
  exact ⟨e1, ⟨hb', e2⟩, e3⟩

@[expose] noncomputable def tag6018 : List ((List Native.Gen × List Native.Gen) × ℕ) :=
  (List.finRange 12).flatMap fun i => (List.range 2).flatMap fun k =>
    [((Cert.gammaW i ++ HS.uW i k, Cert.gammaW i), 0),
     ((Cert.gammaW i ++ HS.uW i k, HS.babyW (HS.bbU i k) ++ HS.hppU i k ++ Cert.gammaW i), 1),
     ((HS.hppU i k, []), 0)]

theorem tag6018_fst : tag6018.map Prod.fst = p6018 := by
  simp [tag6018, p6018, List.map_flatMap]

@[expose] def bbUOK : Bool :=
  (List.finRange 12).all fun i => (List.range 2).all fun k => Nat.blt (HS.bbU i k) 10

theorem stab_body (h : ∀ x ∈ tag6018, TagEq x) (hb : bbUOK = true) :
    (∀ (i : Fin 12), ∀ k, k < 2 → wordLin (HS.uW i k) (HS.vv i) = HS.vv i) ∧
    (∀ (i : Fin 12), ∀ k, k < 2 → HS.bbU i k < 10 ∧
      wordLin (HS.uW i k) (wordLin (Cert.gammaW i) aStarMinus) =
        wordLin (HS.hppU i k ++ Cert.gammaW i) (wordLin (HS.babyW (HS.bbU i k)) aStarMinus)) ∧
    (∀ (i : Fin 12), ∀ k, k < 2 → wordLin (HS.hppU i k) aStar = aStar) := by
  have hm : ∀ (i : Fin 12) k, k < 2 → ∀ y,
      y ∈ [((Cert.gammaW i ++ HS.uW i k, Cert.gammaW i), 0),
        ((Cert.gammaW i ++ HS.uW i k, HS.babyW (HS.bbU i k) ++ HS.hppU i k ++ Cert.gammaW i), 1),
        ((HS.hppU i k, []), 0)] → TagEq y := fun i k hk y hy =>
    h y (List.mem_flatMap.2 ⟨i, List.mem_finRange i,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hy⟩⟩)
  refine ⟨fun i k hk => ?_, fun i k hk => ⟨?_, ?_⟩, fun i k hk => ?_⟩
  · have e := hm i k hk _ List.mem_cons_self
    unfold TagEq at e
    rw [wv_zero, wordLin_append_apply] at e
    exact e
  · exact Nat.le_of_ble_eq_true
      (List.all_eq_true.1 (List.all_eq_true.1 hb i (List.mem_finRange i)) k (List.mem_range.2 hk))
  · have e := hm i k hk _ (List.mem_cons_of_mem _ List.mem_cons_self)
    unfold TagEq at e
    rw [wv_one, wordLin_append_apply, List.append_assoc, wordLin_append_apply] at e
    exact e
  · have e := hm i k hk _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    unfold TagEq at e
    rw [wv_zero, wordLin_nil] at e
    exact e

@[expose] noncomputable def tag6009 : List ((List Native.Gen × List Native.Gen) × ℕ) :=
  (List.range 10).flatMap fun j => (HS.babyBlocks[j]!).map fun b => ((b, []), 0)

theorem tag6009_fst : tag6009.map Prod.fst = p6009 := by
  simp only [tag6009, p6009, List.map_flatMap, List.map_map]
  rfl

@[expose] def blocksOK : Bool :=
  (List.range 10).all fun j => (HS.babyBlocks[j]!).all fun b => b.all fun g => !HS.isTauB g

theorem fix_body (h : ∀ x ∈ tag6009, TagEq x) (hb : blocksOK = true) :
    ∀ j, j < 10 → ∀ b ∈ HS.babyBlocks[j]!,
      (∀ g ∈ b, g ≠ Native.Gen.tau) ∧ wordLin b aStar = aStar := by
  intro j hj b hb'
  refine ⟨notTau_of_all (List.all_eq_true.1 (List.all_eq_true.1 hb j (List.mem_range.2 hj)) b hb'),
    ?_⟩
  have e := h ((b, []), 0)
    (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_map.2 ⟨b, hb', rfl⟩⟩)
  unfold TagEq at e
  rw [wv_zero, wordLin_nil] at e
  exact e

@[expose] noncomputable def babyTag (j : ℕ) : List ((List Native.Gen × List Native.Gen) × ℕ) :=
  (Baby.bo j).U.map (fun w => ((Baby.gW j ++ w, Baby.gW j), 1)) ++
    (List.range (Baby.nrec j)).flatMap (fun r => [true, false].map fun ε =>
      ((Baby.gW j ++ Baby.xW j r ε, Baby.gW (Baby.tgt j r ε)), 1)) ++
    (Baby.jWords j).map (fun w => ((w, []), 0)) ++
    (Baby.bo j).gamma.flatMap (fun sg => Baby.Seg.rec
      (motive := fun _ => List ((List Native.Gen × List Native.Gen) × ℕ))
      (fun w => [((w, []), 0)]) (fun _ => []) sg)

theorem babyTag_fst (j : ℕ) : (babyTag j).map Prod.fst = babyPairs j := by
  simp only [babyTag, babyPairs, List.map_append, List.map_map, List.map_flatMap]
  congr 1
  congr 1
  funext sg
  cases sg <;> rfl

@[expose] noncomputable def babyOK (j : ℕ) : Bool :=
  ((List.range (Baby.nrec j)).all fun r => [true, false].all fun ε => Nat.blt (Baby.tgt j r ε) 10) &&
    ((Baby.jWords j).all fun w => w.all fun g => !HS.isTauB g) &&
    ((Baby.bo j).gamma.all fun sg => Baby.Seg.rec (motive := fun _ => Bool)
      (fun w => w.all fun g => !HS.isTauB g) (fun _ => true) sg)

@[expose] def BabyBody (j : ℕ) : Prop :=
  (∀ w ∈ (Baby.bo j).U, wordLin w (Baby.vv j) = Baby.vv j) ∧
    (∀ r, r < Baby.nrec j → ∀ ε, Baby.tgt j r ε < 10 ∧
      wordLin (Baby.xW j r ε) (Baby.vv j) = Baby.vv (Baby.tgt j r ε)) ∧
    (∀ w ∈ Baby.jWords j, (∀ g ∈ w, g ≠ Native.Gen.tau) ∧ wordLin w aStar = aStar) ∧
    (∀ w, Baby.Seg.blk w ∈ (Baby.bo j).gamma →
      (∀ g ∈ w, g ≠ Native.Gen.tau) ∧ wordLin w aStar = aStar)

theorem baby_body {j : ℕ} (h : ∀ x ∈ babyTag j, TagEq x) (hb : babyOK j = true) : BabyBody j := by
  simp only [babyOK, Bool.and_eq_true] at hb
  obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hb
  refine ⟨fun w hw => ?_, fun r hr ε => ⟨?_, ?_⟩, fun w hw => ⟨?_, ?_⟩, fun w hw => ⟨?_, ?_⟩⟩
  · have e := h _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨w, hw, rfl⟩))))
    unfold TagEq at e
    rw [wv_one, wordLin_append_apply] at e
    exact e
  · exact Nat.le_of_ble_eq_true (List.all_eq_true.1 (List.all_eq_true.1 hb1 r
      (List.mem_range.2 hr)) ε (HS.mem_bool ε))
  · have e := h ((Baby.gW j ++ Baby.xW j r ε, Baby.gW (Baby.tgt j r ε)), 1)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, List.mem_map.2 ⟨ε, HS.mem_bool ε, rfl⟩⟩))))
    unfold TagEq at e
    rw [wv_one, wordLin_append_apply] at e
    exact e
  · exact notTau_of_all (List.all_eq_true.1 hb2 w hw)
  · have e := h ((w, []), 0) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨w, hw, rfl⟩)))
    unfold TagEq at e
    rw [wv_zero, wordLin_nil] at e
    exact e
  · exact notTau_of_all (List.all_eq_true.1 hb3 _ hw)
  · have e := h ((w, []), 0) (List.mem_append_right _
      (List.mem_flatMap.2 ⟨Baby.Seg.blk w, hw, List.mem_singleton.2 rfl⟩))
    unfold TagEq at e
    rw [wv_zero, wordLin_nil] at e
    exact e

@[expose] noncomputable def tag6018v : List ((List Native.Gen × List Native.Gen) × ℕ) :=
  (List.finRange 12).map fun i => ((Cert.gammaW i, Cert.gammaW i), 0)

theorem tag6018v_fst : tag6018v.map Prod.fst = p6018v := by
  simp [tag6018v, p6018v]

theorem tag6018v_length : tag6018v.length = 12 := by
  simp [tag6018v]

@[expose] noncomputable def tag6005v : List ((List Native.Gen × List Native.Gen) × ℕ) :=
  (List.range 10).map fun j => ((Baby.gW j, Baby.gW j), 1)

theorem tag6005v_fst : tag6005v.map Prod.fst = p6005v := by
  simp [tag6005v, p6005v]

theorem tag6005v_length : tag6005v.length = 10 := by
  simp [tag6005v]

theorem trace_inj {R X : ℕ → ℕ}
    (hv : ∀ t (ht : t < tag6018v.length),
      DyRes 7 (trA2 (wordLin tag6018v[t].1.1 (wv tag6018v[t].2))) (R t) ∧
        DyRes 7 (Baby.xStarCoord (wordLin tag6018v[t].1.1 (wv tag6018v[t].2))) (X t))
    (hR : ∀ t, R t < 2 ^ 7 - 1) (hd : ∀ i < 12, ∀ j < 12, R i = R j → i = j) :
    Function.Injective fun i : Fin 12 => trA2 (HS.vv i) := by
  refine res_inj (n := 7) (by norm_num) (R := fun i : Fin 12 => R i) (fun i => ?_)
    (fun i => hR i) (fun i j h => Fin.ext (hd i i.2 j j.2 h))
  have h := (hv i (by rw [tag6018v_length]; exact i.2)).1
  simp only [tag6018v, List.getElem_map, List.getElem_finRange] at h
  exact h

theorem baby_inj {R X : ℕ → ℕ}
    (hv : ∀ t (ht : t < tag6005v.length),
      DyRes 7 (trA2 (wordLin tag6005v[t].1.1 (wv tag6005v[t].2))) (R t) ∧
        DyRes 7 (Baby.xStarCoord (wordLin tag6005v[t].1.1 (wv tag6005v[t].2))) (X t))
    (hR : ∀ t, R t < 2 ^ 7 - 1) (hX : ∀ t, X t < 2 ^ 7 - 1)
    (hd : ∀ i < 10, ∀ j < 10, X i = X j → R i = R j → i = j) :
    Function.Injective fun j : Fin 10 => (Baby.xStarCoord (Baby.vv j), trA2 (Baby.vv j)) := by
  refine res_inj₂ (n := 7) (by norm_num) (R := fun j : Fin 10 => X j) (Q := fun j : Fin 10 => R j)
    (fun j => ?_) (fun j => ?_) (fun j => hX j) (fun j => hR j)
    (fun i j h1 h2 => Fin.ext (hd i i.2 j j.2 h1 h2))
  · have h := (hv j (by rw [tag6005v_length]; exact j.2)).2
    simp only [tag6005v, List.getElem_map, List.getElem_range] at h
    exact h
  · have h := (hv j (by rw [tag6005v_length]; exact j.2)).1
    simp only [tag6005v, List.getElem_map, List.getElem_range] at h
    exact h

end CertificateChecks.KernelKDenseP.Axis

end
