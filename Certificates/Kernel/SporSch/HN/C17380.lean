module

public import Certificates.Kernel.SporSch.HN.C17380K
public import Certificates.Kernel.SporSch.HN.C13609
public import Certificates.Kernel.SporSch.HN.Pt2109
public import CFSG.Certificates.Kernel.RelTabSound
public import CFSG.Sporadic.HNSchreier.ThreeBRels
public import CFSG.Sporadic.HNSchreier.ThreeBGroup

public section

set_option maxRecDepth 20000

namespace CertificateChecks.KernelSporSch.HN17380

open CFSG.KC.ConjKey CFSG.KS.ConjKey CFSG.KS.Ord CFSG.KS.SporSch CFSG.KC.LQT.SecS
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.ThreeBRels CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HN13609 Matrix

local notation "OM" => ordMat 5 133 13 1729
local notation "mm" => CFSG.KC.LL.HN.mm
local notation "G3" => CFSG.KD.HNPt2109.G3F
local notation "ONE" => CFSG.KD.OrdHN.ONE

abbrev Rep (W : ℕ) (g : JH) : Prop := Canon 5 133 13 W ∧ OM W = matJ g

theorem rep_mul {A B : ℕ} {g h : JH} (hA : Rep A g) (hB : Rep B h) : Rep (mm A B) (g * h) := by
  obtain ⟨h1, h2⟩ := HNXP.mm_sound hA.1 hB.1
  exact ⟨h1, by rw [h2, hA.2, hB.2, CFSG.KS.HNArr.matJ_mul]⟩

theorem rep_one : Rep ONE 1 := ⟨(one_sound CFSG.KD.OrdHN.consts).1, HNXP.one_ord⟩

theorem eq_of_rep {A B : ℕ} {g h : JH} (hA : Rep A g) (hB : Rep B h) (e : A = B) : g = h := by
  subst e
  exact matJ_injective (hA.2.symm.trans hB.2)

theorem ne_of_eqK {a b : ℕ} (h : Bool.not (eqK a b) = true) : a ≠ b := by
  intro e
  subst e
  simp [eqK] at h

theorem ne_one_of_key {A : ℕ} {g : JH} (hA : Rep A g) (h : vmHN 1 A ≠ 1) : g ≠ 1 := by
  rintro rfl
  apply h
  have hv := vm_sound e_canon hA.1
  refine vec_inj (by norm_num) hv.1 e_canon ?_
  rw [hv.2, hA.2]
  exact Matrix.vecMul_one _

theorem ne_comm_of_key {A B : ℕ} {g h : JH} (hA : Rep A g) (hB : Rep B h)
    (hne : vmHN (vmHN 1 A) B ≠ vmHN (vmHN 1 B) A) : g * h ≠ h * g := by
  intro e
  apply hne
  have h1 := vm_sound e_canon hA.1
  have h2 := vm_sound h1.1 hB.1
  have h3 := vm_sound e_canon hB.1
  have h4 := vm_sound h3.1 hA.1
  refine vec_inj (by norm_num) h2.1 h4.1 ?_
  rw [h2.2, h1.2, h4.2, h3.2, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hA.2, hB.2,
    ← CFSG.KS.HNArr.matJ_mul, ← CFSG.KS.HNArr.matJ_mul, e]

section Reps


theorem rep_G {l : ℕ} (hl : l < 7) : Rep (G3 l) (c3J l) := G_mat hl

theorem rep_Z : Rep Z (sJ 2) := by
  have h := HNPt2109.S_mat (k := 2) (by norm_num)
  have e : HNPt2109.SJk 2 = sJ 2 := HNPt2085.wJ_sL _ (HNPt2109.letters_ok.1 2 (by norm_num))
  rw [e] at h
  exact h

theorem rep_X4 : Rep X4 (c3J 6 * c3J 1 * c3J 6 * c3J 4 * c3J 0) :=
  rep_mul (rep_mul (rep_mul (rep_mul (rep_G (l := 6) (by norm_num))
    (rep_G (l := 1) (by norm_num))) (rep_G (l := 6) (by norm_num)))
    (rep_G (l := 4) (by norm_num))) (rep_G (l := 0) (by norm_num))

theorem rep_X {i : ℕ} (hi : i < 4) : Rep (XS i) (xs c3J i) := by
  interval_cases i
  · exact rep_G (l := 3) (by norm_num)
  · exact rep_G (l := 5) (by norm_num)
  · exact rep_mul (rep_mul (rep_G (l := 1) (by norm_num)) (rep_G (l := 0) (by norm_num)))
      (rep_G (l := 0) (by norm_num))
  · exact rep_X4

theorem rep_PW {j : ℕ} (hj : j < 10) : Rep (PW j) (pw (sJ 2) c3J j) := by
  interval_cases j
  · exact rep_Z
  · exact rep_mul rep_Z rep_Z
  · exact rep_X (i := 0) (by norm_num)
  · exact rep_mul (rep_X (i := 0) (by norm_num)) (rep_X (i := 0) (by norm_num))
  · exact rep_X (i := 1) (by norm_num)
  · exact rep_mul (rep_X (i := 1) (by norm_num)) (rep_X (i := 1) (by norm_num))
  · exact rep_X (i := 2) (by norm_num)
  · exact rep_mul (rep_X (i := 2) (by norm_num)) (rep_X (i := 2) (by norm_num))
  · exact rep_X (i := 3) (by norm_num)
  · exact rep_mul (rep_X (i := 3) (by norm_num)) (rep_X (i := 3) (by norm_num))

theorem rep_A : Rep A (qa c3J) :=
  rep_mul (rep_mul (rep_G (l := 6) (by norm_num)) (rep_G (l := 3) (by norm_num)))
    (rep_G (l := 0) (by norm_num))

theorem rep_B : Rep B (qb c3J) := by
  have h := CFSG.KS.RelTab.prodL_sound (ρ := matJHom) (rd := ordMat 5 133 13 1729)
    (Ok := Canon 5 133 13)
    (fun hA hB => HNXP.mm_sound hA hB) (M := G3) (g := c3J) (one := ONE)
    (fs := [3, 2, 6, 6, 1, 0, 6, 6, 0, 0]) (by simp) (fun j hj => rep_G (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num))
  exact h

theorem rep_A2 : Rep A2 (qa c3J * qa c3J) := rep_mul rep_A rep_A

end Reps

theorem nRows_eq : HN17380.nRows = ThreeBRels.nRows := rfl

theorem nRows_bounds : ∀ r ∈ ThreeBRels.nRows, r.1 < 7 ∧ r.2.1 < 4 ∧ r.2.2 ≠ [] ∧
    ∀ j ∈ r.2.2, j < 10 := by
  decide

theorem rels17380 : Rels (sJ 2) yE c3J where
  z_cube := eq_of_rep (rep_mul (rep_mul rep_Z rep_Z) rep_Z) rep_one (eqK_spec ch17380_z.1)
  z_ne := ne_one_of_key rep_Z (ne_of_eqK ch17380_z.2)
  x_cube := by
    obtain ⟨h0, h1, h2, h3⟩ := ch17380_r1
    have h3x : ∀ {i : ℕ} (hi : i < 4), Rep (mm (mm (XS i) (XS i)) (XS i))
        (xs c3J i * xs c3J i * xs c3J i) := fun hi =>
      rep_mul (rep_mul (rep_X hi) (rep_X hi)) (rep_X hi)
    intro i hi
    interval_cases i
    · exact eq_of_rep (h3x (i := 0) (by norm_num)) rep_one (eqK_spec h0)
    · exact eq_of_rep (h3x (i := 1) (by norm_num)) rep_one (eqK_spec h1)
    · exact eq_of_rep (h3x (i := 2) (by norm_num)) rep_one (eqK_spec h2)
    · exact eq_of_rep (h3x (i := 3) (by norm_num)) rep_one (eqK_spec h3)
  x13 := eq_of_rep (rep_mul (rep_X (i := 0) (by norm_num)) (rep_X (i := 2) (by norm_num)))
    (rep_mul rep_Z (rep_mul (rep_X (i := 2) (by norm_num)) (rep_X (i := 0) (by norm_num))))
    (eqK_spec ch17380_r2.1)
  x14 := eq_of_rep (rep_mul (rep_X (i := 0) (by norm_num)) (rep_X (i := 3) (by norm_num)))
    (rep_mul rep_Z (rep_mul (rep_X (i := 3) (by norm_num)) (rep_X (i := 0) (by norm_num))))
    (eqK_spec ch17380_r2.2.1)
  x24 := eq_of_rep (rep_mul (rep_X (i := 1) (by norm_num)) (rep_X (i := 3) (by norm_num)))
    (rep_mul rep_Z (rep_mul (rep_X (i := 3) (by norm_num)) (rep_X (i := 1) (by norm_num))))
    (eqK_spec ch17380_r2.2.2.1)
  x34 := eq_of_rep (rep_mul (rep_X (i := 2) (by norm_num)) (rep_X (i := 3) (by norm_num)))
    (rep_mul (rep_mul rep_Z rep_Z)
      (rep_mul (rep_X (i := 3) (by norm_num)) (rep_X (i := 2) (by norm_num))))
    (eqK_spec ch17380_r2.2.2.2.1)
  x12 := eq_of_rep (rep_mul (rep_X (i := 0) (by norm_num)) (rep_X (i := 1) (by norm_num)))
    (rep_mul (rep_X (i := 1) (by norm_num)) (rep_X (i := 0) (by norm_num)))
    (eqK_spec ch17380_r2.2.2.2.2.1)
  x23 := eq_of_rep (rep_mul (rep_X (i := 1) (by norm_num)) (rep_X (i := 2) (by norm_num)))
    (rep_mul (rep_X (i := 2) (by norm_num)) (rep_X (i := 1) (by norm_num)))
    (eqK_spec ch17380_r2.2.2.2.2.2)
  conj := by
    intro r hr
    obtain ⟨hl, hi, hfs, hj⟩ := nRows_bounds r hr
    have h := CFSG.KS.RelTab.relTab_spec ch17380_n r (by rw [nRows_eq]; exact hr)
    exact CFSG.KS.RelTab.relRow_sound (ρ := matJHom) (rd := ordMat 5 133 13 1729)
      (Ok := Canon 5 133 13) (fun _ _ e => matJ_injective e) (fun hA hB => HNXP.mm_sound hA hB) hfs (rep_G hl)
      (rep_X hi) (fun j hjm => rep_PW (hj j hjm)) h
  a_four := eq_of_rep (rep_mul rep_A2 rep_A2) rep_one (eqK_spec ch17380_q.1)
  a_sq_ne := ne_one_of_key rep_A2 (ne_of_eqK ch17380_q.2.1)
  b_sq := eq_of_rep (rep_mul rep_B rep_B) rep_A2 (eqK_spec ch17380_q.2.2.1)
  aba := eq_of_rep (rep_mul (rep_mul rep_A rep_B) rep_A) rep_B (eqK_spec ch17380_q.2.2.2.1)
  a_sq_x := ne_comm_of_key rep_A2 (rep_X (i := 0) (by norm_num)) (ne_of_eqK ch17380_q.2.2.2.2)
  c0_cube := eq_of_rep (rep_mul (rep_mul (rep_G (l := 0) (by norm_num))
    (rep_G (l := 0) (by norm_num))) (rep_G (l := 0) (by norm_num))) rep_one (eqK_spec ch17380_w)
  y_x := ne_comm_of_key Y_mat (rep_X (i := 0) (by norm_num)) (ne_of_eqK ch17380_y)

theorem facts17380 :
    ∃ R : Subgroup JH, R ≤ CJ (sJ 2) ∧ Nat.card R = 243 ∧
      (∀ g ∈ CJ (sJ 2), ∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧
      CJ (sJ 2) ⊓ Subgroup.centralizer (R : Set JH) ≤ R :=
  ThreeBGroup.threeB card_CJ_s3 le_rfl (mem_CJ.2 rfl) (fun _ hl => mem_CJ.2 (c3J_comm hl).symm)
    rfl HN13609.facts.2 rels17380

end CertificateChecks.KernelSporSch.HN17380

end
