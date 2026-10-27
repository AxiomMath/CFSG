module

public import Certificates.Kernel.E6TwD4T2.Glue
public import Certificates.Kernel.E6TwD4T2.Rows
import Certificates.Kernel.E6TwD4T2.Checks

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelE6TwD4T2

open CFSG.KD.E6TwD4T2 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem reps_check : twD4T2RepsOK () = true := by decide +kernel

theorem moves_check : twD4T2Elems.all (fun e => decodeT Tag.E6.rank e.1 == List.range Tag.E6.rank ||
    twD4T2Moves (decodeT Tag.E6.rank e.1) e.2.1 e.2.2) = true := by decide +kernel

theorem words_check : (twD4T2Words.map twD4T2WordTuple).all (fun t =>
    twD4T2Fixes (vec3 (τ := .E6) twD4T2F0) t && e6ScTest e6Certificate twD4T2F0 t) = true := by
  decide +kernel

theorem wts_check : (twD4T2Words.map twD4T2WordTuple == wts) = true := by decide +kernel

theorem wts_lt_check : (wts.all fun t => (List.range 6).all fun j => decide (t.getD j 0 < 72)) =
    true := by decide +kernel

theorem rows_check : (sig.zip rows).all (fun p => twD4T2RowOK p.1 p.2) = true := by decide +kernel

theorem rows_shape_check : (sig.length == rows.length && sig.all (fun b => decide (b < 72)) &&
    rows.all fun r => r.length == 72) = true := by decide +kernel

theorem vecs_check : (twD4T2Vecs ()).Nodup ∧ (twD4T2Vecs ()).length = 72 := by decide +kernel

theorem closed_check : twD4T2Closed (twD4T2Elems.map Prod.fst) (sig.zip rows)
    (KTree.ofSorted (twD4T2Elems.map Prod.fst)) = true := by decide +kernel

theorem row_eq {b : ℕ} {row : List ℕ} (hlen : row.length = 72) (h : twD4T2RowOK b row = true) :
    twD4T2Row (twD4T2Vecs ()) b = row := by
  have hn : e6Certificate.roots.length = 72 := by decide +kernel
  obtain ⟨hnd, hvl⟩ := vecs_check
  unfold twD4T2RowOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, hn] at h
  apply List.ext_getElem
  · simp [twD4T2Row, hn, hlen]
  intro k hk1 hk2
  have hk : k < 72 := by simpa [twD4T2Row, hn] using hk1
  obtain ⟨hlt, heq⟩ := h k hk
  simp only [twD4T2Row, List.getElem_map, List.getElem_range]
  rw [← List.getD_eq_getElem row 0 hk2]
  have hvm : ∀ m (hm : m < (twD4T2Vecs ()).length),
      (twD4T2Vecs ())[m] = List.ofFn (e6Certificate.root m) := by
    intro m hm
    simp [twD4T2Vecs]
  have hf : (twD4T2Vecs ()).findIdx? (fun x => x == List.ofFn (e6Certificate.root k -
      corootPair (e6Certificate.root b) (e6Certificate.root k) • e6Certificate.root b)) =
      some (row.getD k 0) := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨by omega, ?_, fun j hj => ?_⟩
    · rw [hvm, beq_iff_eq, heq]
    · rw [hvm, beq_iff_eq, ← heq, ← hvm _ (by omega), ← hvm (row.getD k 0) (by omega),
        hnd.getElem_inj]
      omega
  rw [hf]
  rfl

theorem brs_aux : ∀ (S : List ℕ) (R : List (List ℕ)), S.length = R.length →
    (∀ r ∈ R, r.length = 72) → (∀ p ∈ S.zip R, twD4T2RowOK p.1 p.2 = true) →
    S.map (fun b => (b, twD4T2Row (twD4T2Vecs ()) b)) = S.zip R := by
  intro S
  induction S with
  | nil => intro R _ _ _; simp
  | cons b S ih =>
    intro R hl hrl hr
    obtain _ | ⟨r, R⟩ := R
    · simp at hl
    · simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq, Prod.mk.injEq, true_and]
      simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hr
      refine ⟨row_eq (hrl r (by simp)) hr.1, ?_⟩
      exact ih R (by simpa using hl) (fun x hx => hrl x (by simp [hx])) hr.2

theorem brs_eq : (twD4T2Sig ()).map (fun b => (b, twD4T2Row (twD4T2Vecs ()) b)) = sig.zip rows := by
  rw [sig_eq]
  have hr := rows_check
  have hs := rows_shape_check
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hs
  simp only [List.all_eq_true] at hr
  exact brs_aux sig rows hs.1.1 hs.2 hr

theorem arr_getD {α : Type} (l : List α) (k : ℕ) (d : α) : l.toArray.getD k d = l.getD k d := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem ztab_getD {S : List ℕ} {k : ℕ} (hk : k < 3 ^ Tag.E6.rank) :
    (twD4T2ZTab S).getD k [] = (List.range S.length).filter fun i =>
      decide (triPairing (vec3OfIndex (τ := .E6) k) (e6Certificate.root (S.getD i 0)) = 0) := by
  unfold twD4T2ZTab
  rw [arr_getD, getD_range_map' _ _ hk]

theorem gtab_getD {ts : List (List ℕ)} {k : ℕ} (hk : k < 3 ^ Tag.E6.rank) :
    (twD4T2GTab ts).getD k false = ts.any (twD4T2Fixes (vec3OfIndex (τ := .E6) k)) := by
  unfold twD4T2GTab
  rw [arr_getD, getD_range_map' _ _ hk]

theorem idx3_spec (v : Fin Tag.E6.rank → ZMod 3) :
    twIdx3 v < 3 ^ Tag.E6.rank ∧ vec3OfIndex (τ := .E6) (twIdx3 v) = v := by
  let F : Fin Tag.E6.rank → Fin 3 := fun j => ⟨(v j).val, ZMod.val_lt (v j)⟩
  have hF : twIdx3 v = (finFunctionFinEquiv F : ℕ) := by
    rw [finFunctionFinEquiv_apply]
    rfl
  refine ⟨hF ▸ (finFunctionFinEquiv F).2, ?_⟩
  funext j
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv F) j
  rw [Equiv.symm_apply_apply] at h
  simp only [vec3OfIndex]
  rw [hF, ← h]
  simp [F]

theorem dot3_vec (k : ℕ) (w : List ℕ) : ((dot3 k w : ℕ) : ZMod 3) =
    ∑ j : Fin Tag.E6.rank, vec3OfIndex (τ := .E6) k j * ((w.getD j 0 : ℕ) : ZMod 3) := by
  rw [dot3_cast]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => ((k / 3 ^ j % 3 : ℕ) : ZMod 3) * ((w.getD j 0 : ℕ) : ZMod 3)) 6).symm

theorem line_ok {k₁ k₂ : ℕ} (a b : ZMod 3) {t : List ℕ} (ht : t ∈ wts)
    (h : ∀ w ∈ wv r3 t, a * (dot3 k₁ w : ZMod 3) + b * (dot3 k₂ w : ZMod 3) = 0) :
    (twD4T2GTab (twD4T2Words.map twD4T2WordTuple)).getD
      (twIdx3 (a • vec3OfIndex (τ := .E6) k₁ + b • vec3OfIndex (τ := .E6) k₂)) false = true := by
  obtain ⟨hlt, hv⟩ := idx3_spec (a • vec3OfIndex (τ := .E6) k₁ + b • vec3OfIndex (τ := .E6) k₂)
  rw [gtab_getD hlt, List.any_eq_true, beq_iff_eq.1 wts_check]
  refine ⟨t, ht, ?_⟩
  have hlt72 := wts_lt_check
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hlt72
  rw [fixes_iff _ (hlt72 t ht)]
  intro w hw
  rw [← nat_zmod3 (dot3_lt _ _), dot3_vec, hv, ← h w hw, dot3_vec, dot3_vec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem neg_cast {d : ℕ} (hd : d < 3) : (d : ZMod 3) + (((3 - d) % 3 : ℕ) : ZMod 3) = 0 := by
  interval_cases d <;> decide

theorem pairs_ok : twD4T2PairsOK (twD4T2ZTab (twD4T2Sig ()))
    (twD4T2GTab (twD4T2Words.map twD4T2WordTuple)) = true := by
  have hs := pairsK_sound ch214101_planes ch214101_r3 ch214101_tab ch214101_sig ch214101_g
    ch214101_pairs
  have hsl := rows_shape_check
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hsl
  have hs72 := hsl.1.2
  unfold twD4T2PairsOK
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true]
  intro k₁ hk₁ k₂ hk₂
  rw [ztab_getD hk₁, ztab_getD hk₂, sig_eq]
  have hmw : ∀ {ws}, ws ∈ wts.map (wv r3) → ∃ t ∈ wts, ws = wv r3 t := by
    intro ws hws
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hws
    exact ⟨t, ht, rfl⟩
  have hco : ∀ ab ∈ [((1 : ZMod 3), (0 : ZMod 3)), (0, 1), (1, 1), (1, 2)], ab ∈ twD4T2Coeffs := by
    intro ab hab
    exact hab
  rcases hs k₁ hk₁ k₂ hk₂ with h | ⟨p, hp, h1, h2⟩ | h | h | h
  · obtain ⟨ws, hws, h⟩ := h
    obtain ⟨t, ht, rfl⟩ := hmw hws
    exact Or.inr ⟨(1, 0), hco _ (by simp), line_ok 1 0 ht fun w hw => by simp [h w hw]⟩
  · left
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hp72 : sig[i] < 72 := hs72 _ hp
    have hz : ∀ k, dot3 k (r3.getD sig[i] []) = 0 →
        i ∈ (List.range sig.length).filter fun i' =>
          decide (triPairing (vec3OfIndex (τ := .E6) k) (e6Certificate.root (sig.getD i' 0)) = 0) := by
      intro k hk
      rw [List.mem_filter, List.mem_range, List.getD_eq_getElem sig 0 hi, pair_root k hp72, hk]
      exact ⟨hi, by simp⟩
    exact ⟨i, hz k₁ h1, List.contains_iff_mem.2 (hz k₂ h2)⟩
  · obtain ⟨ws, hws, h⟩ := h
    obtain ⟨t, ht, rfl⟩ := hmw hws
    exact Or.inr ⟨(0, 1), hco _ (by simp), line_ok 0 1 ht fun w hw => by simp [h w hw]⟩
  · obtain ⟨ws, hws, h⟩ := h
    obtain ⟨t, ht, rfl⟩ := hmw hws
    refine Or.inr ⟨(1, 1), hco _ (by simp), line_ok 1 1 ht fun w hw => ?_⟩
    rw [h w hw, one_mul, one_mul]
    exact neg_cast (dot3_lt _ _)
  · obtain ⟨ws, hws, h⟩ := h
    obtain ⟨t, ht, rfl⟩ := hmw hws
    refine Or.inr ⟨(1, 2), hco _ (by simp), line_ok 1 2 ht fun w hw => ?_⟩
    rw [h w hw]
    generalize ((dot3 k₁ w : ℕ) : ZMod 3) = x
    revert x
    decide

end CertificateChecks.KernelE6TwD4T2
