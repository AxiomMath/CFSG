module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import CFSG.Monster.AxisCount.DenseModFive

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP

open CFSG.Monster CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.AGLEmbedding.Norton.MON5_7

theorem size_scale (f : ℕ) (A : Array ℤ) : (Native.scale f A).size = A.size := by
  simp [Native.scale]

theorem size_reduceN : ∀ (n : ℕ) (v : Native.DVec), (Native.reduceN n v).D.size = v.D.size
  | 0, v => rfl
  | n + 1, v => by
    unfold Native.reduceN
    split
    · rw [size_reduceN n]
      simp
    · rfl

theorem size_reduce (v : Native.DVec) : v.reduce.D.size = v.D.size := size_reduceN _ _

theorem size_scatterAt (off n : ℕ) (T : ℕ → List (ℕ × ℤ)) (D : Array ℤ) :
    (Native.scatterAt off n T D).size = n := by
  unfold Native.scatterAt
  have inner : ∀ (L : List (ℕ × ℤ)) (x : ℤ) (out : Array ℤ),
      (L.foldl (fun out' t => if t.1 < n then out'.modify t.1 (fun y => y + t.2 * x) else out')
        out).size = out.size := by
    intro L x
    induction L with
    | nil => intro out; rfl
    | cons t L ih =>
      intro out
      rw [List.foldl_cons, ih]
      split <;> simp
  have outer : ∀ (L : List ℕ) (out : Array ℤ), (L.foldl (fun out p =>
      let x := D[off + p]!
      if x == 0 then out
      else (T p).foldl
        (fun out' t => if t.1 < n then out'.modify t.1 (fun y => y + t.2 * x) else out') out)
      out).size = out.size := by
    intro L
    induction L with
    | nil => intro out; rfl
    | cons p L ih =>
      intro out
      rw [List.foldl_cons, ih]
      dsimp only
      split
      · rfl
      · exact inner _ _ _
  rw [outer]
  simp

theorem size_applyGen (c : Native.Ctx) (g : Native.Gen) (v : Native.DVec) :
    (Native.applyGen c g v).D.size = 196884 := by
  cases g with
  | tau => simp only [Native.applyGen, Native.applyTau, size_scatterAt]
  | _ =>
    simp only [Native.applyGen, Native.applyGD, Array.size_append, size_scale, size_scatterAt,
      Native.latA, Array.size_ofFn]

theorem size_evalWordC (c : Native.Ctx) :
    ∀ (w : List Native.Gen) (v : Native.DVec), v.D.size = 196884 →
      (Native.evalWordC c w v).D.size = 196884
  | [], _, h => h
  | g :: w, v, _ => by
    rw [evalWordC_cons]
    exact size_evalWordC c w _ (by rw [size_reduce, size_applyGen])

theorem size_aV : (aV ()).D.size = 196884 := by simp only [aV, Array.size_ofFn]
theorem size_bV : (bV ()).D.size = 196884 := by simp only [bV, Array.size_ofFn]
theorem size_wV : (wV ()).D.size = 196884 := by simp only [wV, Array.size_ofFn]

theorem eqv_of_interp_eq {u v : Native.DVec}
    (hu : u.D.size = 196884) (hv : v.D.size = 196884) (h : interp u = interp v) :
    u.eqv v = true := by
  unfold Native.DVec.eqv
  rw [beq_iff_eq]
  apply Array.ext
  · rw [size_scale, size_scale, hu, hv]
  · intro k h1' h2
    have h1 : k < 196884 := by rw [size_scale, hu] at h1'; exact h1'
    have hc := cf_eq_of_interp_eq h h1
    unfold cf at hc
    have g1 : (Native.scale (max u.e v.e - u.e) u.D)[k] =
        (Native.scale (max u.e v.e - u.e) u.D).getD k 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1', Option.getD_some]
    have g2 : (Native.scale (max u.e v.e - v.e) v.D)[k] =
        (Native.scale (max u.e v.e - v.e) v.D).getD k 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some]
    rw [g1, g2, scale_getD_all, scale_getD_all]
    have p1 : (2 : ℚ) ^ (max u.e v.e) = 2 ^ u.e * 2 ^ (max u.e v.e - u.e) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_max_left _ _)]
    have p2 : (2 : ℚ) ^ (max u.e v.e) = 2 ^ v.e * 2 ^ (max u.e v.e - v.e) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_max_right _ _)]
    have hq : (u.D.getD k 0 : ℚ) * 2 ^ (max u.e v.e - u.e) =
        (v.D.getD k 0 : ℚ) * 2 ^ (max u.e v.e - v.e) := by
      have hu0 : (2 : ℚ) ^ u.e ≠ 0 := pow_ne_zero _ two_ne_zero
      have hv0 : (2 : ℚ) ^ v.e ≠ 0 := pow_ne_zero _ two_ne_zero
      calc (u.D.getD k 0 : ℚ) * 2 ^ (max u.e v.e - u.e)
          = (u.D.getD k 0 : ℚ) / 2 ^ u.e * 2 ^ (max u.e v.e) := by
            rw [p1]; field_simp
        _ = (v.D.getD k 0 : ℚ) / 2 ^ v.e * 2 ^ (max u.e v.e) := by rw [hc]
        _ = (v.D.getD k 0 : ℚ) * 2 ^ (max u.e v.e - v.e) := by
            rw [p2]; field_simp
    exact_mod_cast hq

theorem eqv_evalWord {w₁ w₂ : List Native.Gen}
    (h₁ : ∀ g ∈ w₁, g.validB = true) (h₂ : ∀ g ∈ w₂, g.validB = true)
    (h : wordLin w₁ = wordLin w₂) {v : Native.DVec} (hv : v.D.size = 196884) :
    (Native.evalWord w₁ v).eqv (Native.evalWord w₂ v) = true :=
  eqv_of_interp_eq (size_evalWordC _ w₁ v hv) (size_evalWordC _ w₂ v hv) (by
    rw [evalWord_sound w₁ h₁, evalWord_sound w₂ h₂, h])

theorem agree_of_wordLin {w₁ w₂ : List Native.Gen}
    (h₁ : ∀ g ∈ w₁, g.validB = true) (h₂ : ∀ g ∈ w₂, g.validB = true)
    (h : wordLin w₁ = wordLin w₂) : agree w₁ w₂ = true := by
  unfold agree
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨h₁, h₂⟩, eqv_evalWord h₁ h₂ h size_aV⟩, eqv_evalWord h₁ h₂ h size_bV⟩,
    eqv_evalWord h₁ h₂ h size_wV⟩

theorem agreeAll_of_wordLin
    {ps : List (List Native.Gen × List Native.Gen)}
    (hv : ∀ p ∈ ps, (∀ g ∈ p.1, g.validB = true) ∧ ∀ g ∈ p.2, g.validB = true)
    (h : ∀ p ∈ ps, wordLin p.1 = wordLin p.2) : agreeAll ps = true :=
  List.all_eq_true.2 fun p hp => agree_of_wordLin (hv p hp).1 (hv p hp).2 (h p hp)

theorem moveCheckAux_of_res5 {u v : Native.DVec} {k : ℕ} (hk : k < 196884)
    (h : DVec.res5 u k ≠ DVec.res5 v k) : EdgeNoncomm.moveCheckAux u v = true := by
  unfold EdgeNoncomm.moveCheckAux
  rw [List.any_eq_true]
  by_contra hn
  push Not at hn
  have e := hn k (List.mem_range.2 hk)
  simp only [bne_iff_ne, ne_eq, not_not] at e
  apply h
  apply res5_eq_of_cf_eq
  unfold cf
  have hu0 : (2 : ℚ) ^ u.e ≠ 0 := pow_ne_zero _ two_ne_zero
  have hv0 : (2 : ℚ) ^ v.e ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [div_eq_div_iff hu0 hv0]
  exact_mod_cast e

end CertificateChecks.KernelKDenseP

end
