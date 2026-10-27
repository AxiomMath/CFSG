module

public import Certificates.Kernel.SmithL6K.Pins
public import Certificates.Kernel.SmithL6K.ChecksF
public import CFSG.Certificates.Kernel.SmithL6KFSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.CollK CFSG.SmithL6.Kernel
open CFSG.SmithE (applyCols)

theorem apK_tcl {k : Nat} (hk : k < 1953) (x : Nat) :
    apK (tcl.getD k []) x = applyCols (tvCols k) x := by
  rw [← tvCols_eq hk, ← applyCols_toArray, Array.toArray_toList]

theorem kind_eq {l : Nat} (hl : l < 1953) :
    mfPairKind 0 l = kindC (tvc.getD 0 0) (tvc.getD l 0) := by
  rw [mfPairKind_eq (by decide) hl, tvPair_code (by decide), tvPair_code hl]

theorem kill_tcl {F : List Nat} {k : Nat} (hk : k < 1953) (h : killK F (tcl.getD k []) = true) :
    ∀ c < 2 ^ 20, apK F (applyCols (tvCols k) c ^^^ c) = 0 :=
  killK_sound (tvCols_eq hk) (tvCols_size k) h

@[expose] noncomputable def fx0 : Nat := (fe.getD 0 (0, 0, 0, [])).2.1

theorem fRec_parts {e : Nat × Nat × Nat × List Nat} (h : fRecK tvc tcl wtd fx0 e = true) :
    e.1 < 1395 ∧ wt e.1 = e.2.1 ∧ e.2.2.1 < 2 ^ 20 ∧
      applyCols (tvCols 0) e.2.2.1 ^^^ e.2.2.1 = e.2.1 ∧
      (∀ r ∈ e.2.2.2, r < 1953 ∧ mfPairKind 0 r = 0) ∧
      e4fApplyWord e.2.2.2 fx0 = e.2.1 ∧ e4fApplyWord e.2.2.2.reverse e.2.1 = fx0 := by
  simp only [fRecK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hi, hw⟩, hc⟩, hpre⟩, hr⟩, hw1⟩, hw2⟩ := h
  have hr' : ∀ r ∈ e.2.2.2, r < 1953 ∧ mfPairKind 0 r = 0 :=
    fun r hm => ⟨(hr r hm).1, by rw [kind_eq (hr r hm).1]; exact (hr r hm).2⟩
  have hlt : ∀ r ∈ e.2.2.2, r < 1953 := fun r hm => (hr r hm).1
  have hlt' : ∀ r ∈ e.2.2.2.reverse, r < 1953 := fun r hm => hlt r (List.mem_reverse.mp hm)
  refine ⟨hi, by rw [wt_eq hi]; exact hw, hc, by rw [← apK_tcl (by decide)]; exact hpre, hr', ?_,
    ?_⟩
  · rw [← wordK_eq (fun r hr => tvCols_eq hr) hlt]
    exact hw1
  · rw [← wordK_eq (fun r hr => tvCols_eq hr) hlt']
    exact hw2

theorem fWord_parts : killK fs0 (tcl.getD 0 []) = true ∧
    (∀ x ∈ wtd, apK fs0 x ≠ 0 ∨ ∃ e ∈ fe, e.2.1 = x) ∧
    ∀ e ∈ fe, fRecK tvc tcl wtd fx0 e = true := by
  have h := fWord_ok
  simp only [fWordK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.any_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cover {i : Nat} (hi : i < 1395) (h : ∃ c < 2 ^ 20, applyCols (tvCols 0) c ^^^ c = wt i) :
    ∃ e ∈ fe, e.2.1 = wt i := by
  obtain ⟨hk, hall, -⟩ := fWord_parts
  obtain ⟨c, hc, he⟩ := h
  have hz := kill_tcl (by decide) hk c hc
  rw [he] at hz
  have hm : wt i ∈ wtd := by
    rw [wt_eq hi, getD_of_lt (by rw [wtd_length]; exact hi)]
    exact List.getElem_mem _
  rcases hall _ hm with h | h
  · exact absurd hz h
  · exact h

theorem word0_holds : ∀ i < 1395, ∀ j < 1395,
    (∃ c < 2 ^ 20, applyCols (tvCols 0) c ^^^ c = wt i) →
    (∃ c < 2 ^ 20, applyCols (tvCols 0) c ^^^ c = wt j) →
    ∃ w : List Nat, (∀ r ∈ w, r < 1953 ∧ mfPairKind 0 r = 0) ∧ e4fApplyWord w (wt i) = wt j := by
  intro i hi j hj hEi hEj
  obtain ⟨ei, hei, hxi⟩ := cover hi hEi
  obtain ⟨ej, hej, hxj⟩ := cover hj hEj
  obtain ⟨-, -, -, -, hri, -, hbi⟩ := fRec_parts (fWord_parts.2.2 ei hei)
  obtain ⟨-, -, -, -, hrj, hfj, -⟩ := fRec_parts (fWord_parts.2.2 ej hej)
  refine ⟨ej.2.2.2 ++ ei.2.2.2.reverse, fun r hr => ?_, ?_⟩
  · rcases List.mem_append.mp hr with h | h
    · exact hrj r h
    · exact hri r (List.mem_reverse.mp h)
  · rw [e4fApplyWord_append, ← hxi, hbi, hfj, hxj]

theorem plane0_holds : ∀ l < 1953, mfPairKind 0 l = 2 → ∃ i < 1395,
    (∃ c < 2 ^ 20, applyCols (tvCols 0) c ^^^ c = wt i) ∧
    applyCols (tvCols l) (wt i) = wt i ∧
    ¬ ∃ c < 2 ^ 20, applyCols (tvCols l) c ^^^ c = wt i := by
  intro l hl hk
  have h := fPlane_ok
  simp only [fPlaneK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hC, hL⟩, hP⟩, hall⟩ := h
  have hl1 : l < (tvc.zip (tcl.zip fp)).length := by
    simp only [List.length_zip, hC, hL, hP, Nat.min_self]
    exact hl
  have hq := hall _ (List.getElem_mem hl1)
  simp only [List.getElem_zip] at hq
  have hc : tvc[l]'(by rw [hC]; exact hl) = tvc.getD l 0 := (getD_of_lt _).symm
  have ht : tcl[l]'(by rw [hL]; exact hl) = tcl.getD l [] := (getD_of_lt _).symm
  rw [hc, ht, ← kind_eq hl, hk] at hq
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, bne_iff_ne, ne_eq] at hq
  obtain ⟨⟨⟨ha, hfix⟩, hkill⟩, hnz⟩ := hq
  set e := fe.getD (fp[l]'(by rw [hP]; exact hl)).1 (0, 0, 0, []) with he
  have hem : e ∈ fe := by
    rw [he, getD_of_lt ha]
    exact List.getElem_mem _
  obtain ⟨hi, hwt, hc0, hpre, -⟩ := fRec_parts (fWord_parts.2.2 e hem)
  refine ⟨e.1, hi, ⟨_, hc0, by rw [hpre, hwt]⟩, ?_, ?_⟩
  · rw [hwt, ← apK_tcl hl]
    exact hfix
  · rintro ⟨c, hc', hce⟩
    have hz := kill_tcl hl hkill c hc'
    rw [hce, hwt] at hz
    exact hnz hz

end CertificateChecks.KernelSmithL6K
