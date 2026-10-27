module

public import CFSG.Sporadic.Bridge.SuzMats
public import Certificates.Kernel.Sporadic.SuzBridge.Checks

public section

namespace CertificateChecks.KernelSpor.SuzBridge

open CFSG CFSG.KC.Ord CFSG.KS.Ord CFSG.KD.SuzB CFSG.Sporadic.Bridge.SuzMats

noncomputable abbrev Y (M : ℕ) : Mat64 := ordMat 3 64 10 640 M

noncomputable abbrev X (g : ℕ) : Mat64 := Y (RB g)

noncomputable abbrev G (g : ℕ) : Mat64 := X (g + 1)

theorem hom : (∀ g < 9, X (g + 1) * X (9 + 1 + g) = 1) ∧
    ∀ v ∈ rels, (v.map fun x => Y (letM RB 9 x)).prod = 1 := by
  have hn : lenRels rels = 43 := Nat.eq_of_beq_eq_true relN
  have hall := List.all_eq_true.1 relsAll
  have h := rels_sound (hnb := rfl) consts roots invs relB fun r hr =>
    Or.inl (hall r (List.mem_range.2 (by rw [hn] at hr; exact hr)))
  exact h

theorem inv_G {g : ℕ} (hg : g < 9) : (G g)⁻¹ = X (9 + 1 + g) :=
  Matrix.inv_eq_right_inv (hom.1 g hg)

theorem inv_G_mul {g : ℕ} (hg : g < 9) : (G g)⁻¹ * G g = 1 := by
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse (hom.1 g hg))

theorem letM_false (R : ℕ → ℕ) (n g : ℕ) : letM R n (g, false) = R (n + 1 + g) := rfl

theorem letM_true (R : ℕ → ℕ) (n g : ℕ) : letM R n (g, true) = R (g + 1) := rfl

theorem letM_eq (x : ℕ × Bool) (hx : x.1 < 9) :
    Y (letM RB 9 x) = if x.2 then G x.1 else (G x.1)⁻¹ := by
  obtain ⟨g, s⟩ := x
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [letM_false, inv_G hx]
  · simp only [↓reduceIte]
    rw [letM_true]

theorem bounded : ∀ v ∈ rels, ∀ x ∈ v, x.1 < 9 := by decide +kernel

theorem img_letters : ∀ k < 7, ∀ x ∈ wordAt imgWords k, x.1 < 2 := by decide +kernel

theorem surj_letters : ∀ j < 2, ∀ x ∈ wordAt surjWords j, x.1 < 7 := by decide +kernel

theorem suz_letters : ∀ v ∈ suzRels, ∀ x ∈ v, x.1 < 7 := by decide +kernel

theorem wordM_G {v : List (ℕ × Bool)} (hv : v ∈ rels) : wordM G v = 1 := by
  rw [← hom.2 v hv]
  unfold wordM
  exact congrArg List.prod
    (List.map_congr_left fun x hx => (letM_eq x (bounded v hv x hx)).symm)

theorem eq_of_rel {u : List (ℕ × Bool)} {g : ℕ} (hg : g < 9) (h : u ++ [(g, false)] ∈ rels) :
    wordM G u = G g := by
  have h1 := wordM_G h
  rw [wordM_append, wordM_inv_letter] at h1
  calc wordM G u = wordM G u * ((G g)⁻¹ * G g) := by rw [inv_G_mul hg, Matrix.mul_one]
    _ = G g := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem mem_img {k : ℕ} (hk : k < 7) : wordAt imgWords k ++ [(k + 2, false)] ∈ rels := by
  unfold rels
  exact List.mem_append_left _
    (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))

theorem mem_surj {j : ℕ} (hj : j < 2) : shiftW 2 (wordAt surjWords j) ++ [(j, false)] ∈ rels := by
  unfold rels
  exact List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))

theorem mem_suz {v : List (ℕ × Bool)} (hv : v ∈ suzRels) : shiftW 2 v ∈ rels := by
  unfold rels
  exact List.mem_append_right _ (List.mem_map.2 ⟨v, hv, rfl⟩)

theorem seeds_eq {g : ℕ} (hg : g < 2) : seeds g = G g := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · simp only [seeds, ↓reduceIte]
    exact seedA
  · simp only [seeds, one_ne_zero, ↓reduceIte]
    exact seedB

theorem img_eq {k : ℕ} (hk : k < 7) : img k = G (k + 2) := by
  unfold img
  rw [wordM_congr (G' := G) fun x hx => seeds_eq (img_letters k hk x hx)]
  exact eq_of_rel (by omega) (mem_img hk)

theorem relatorLetters_eq : TauCeti.Sporadic.suzPresentation.relatorLetters = suzRels := by
  rw [TauCeti.Sporadic.suzPresentation_relatorLetters]
  rfl

theorem surj_eq {j : ℕ} (hj : j < 2) : wordM img (wordAt surjWords j) = G j := by
  have h := eq_of_rel (by omega) (mem_surj hj)
  rw [wordM_shiftW] at h
  rw [← h]
  exact wordM_congr fun x hx => img_eq (surj_letters j hj x hx)

theorem facts : Facts where
  rels v hv := by
    rw [relatorLetters_eq] at hv
    have h := wordM_G (mem_suz hv)
    rw [wordM_shiftW] at h
    rw [← h]
    exact wordM_congr fun x hx => img_eq (suz_letters v hv x hx)
  surjA := by
    rw [surj_eq (by norm_num)]
    exact seedA.symm
  surjB := by
    rw [surj_eq (by norm_num)]
    exact seedB.symm

end CertificateChecks.KernelSpor.SuzBridge

end
