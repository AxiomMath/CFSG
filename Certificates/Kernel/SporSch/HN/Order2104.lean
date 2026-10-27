
module

public import CFSG.Certificates.Kernel.SporSch.HNArr
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public import CFSG.Sporadic.HNSchreier.Seeds
public import Certificates.Kernel.SporSch.HN.Intr2098
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CertificateChecks.KernelSporSch.HNOrd2104

open CFSG.KS.HNArr CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native

theorem ppow_arrJ (g : JH) : ∀ e, ppow nPts (arrJ g) e = arrJ (g ^ e)
  | 0 => by rw [ppow, pid_arrJ, pow_zero]
  | e + 1 => by rw [ppow, ppow_arrJ g e, pcomp_arrJ, pow_succ]

theorem peq_one_iff (g : JH) :
    peq nPts (arrJ g) (pid nPts) = true ↔ g = 1 := by
  constructor
  · intro h
    have hx : ∀ x : X, g • x = x := fun x => by
      have := CFSG.ONSchreier.allBelowN_iff.1 h x.val x.isLt
      rw [beq_iff_eq, arrJ_get _ x.isLt, pid_arrJ, arrJ_get _ x.isLt, gi_one x.isLt,
        gi_of_lt _ x.isLt] at this
      exact Fin.ext this
    have := hns_faithful
    exact eq_of_smul_eq_smul fun x => by rw [hx x, one_smul]
  · rintro rfl
    rw [pid_arrJ]
    exact peq_refl _ _

theorem peq_one : peq nPts (arrJ 1) (pid nPts) = true :=
  (peq_one_iff 1).2 rfl

theorem peq_ne_one {g : JH} (hg : g ≠ 1) :
    peq nPts (arrJ g) (pid nPts) = false :=
  Bool.eq_false_iff.2 fun h => hg ((peq_one_iff g).1 h)

@[expose] noncomputable def gAB (j : ℕ) : JH := if j = 0 then aJ else bJ

theorem gAB0 : gAB 0 = aJ := if_pos rfl

theorem gAB1 : gAB 1 = bJ := if_neg (by norm_num)

theorem arrs_AB : ArrsOK 2 #[arrJ aJ, arrJ bJ] #[arrJ aJ⁻¹, arrJ bJ⁻¹] gAB := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · refine ⟨?_, ?_⟩ <;> simp only [List.getElem!_toArray, List.getElem!_cons_zero, gAB0]
  · refine ⟨?_, ?_⟩ <;>
      simp only [List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero, gAB1]

theorem word_gen (gs : ℕ → JH) : wJ gs conjProdWord =
    gs 0 * (gs 0 * gs 1 * gs 1 * gs 0 * gs 1 * gs 0 * gs 1 * gs 0 * gs 1 * gs 0 * gs 1 * gs 0)⁻¹ *
      gs 1 * (gs 0 * gs 1 * gs 1 * gs 0 * gs 1 * gs 0 * gs 1 * gs 0 * gs 1 * gs 0 * gs 1 * gs 0) := by
  simp only [conjProdWord, wJ, lJ]
  norm_num
  group

noncomputable abbrev gJ : JH := aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ

theorem word_X : wJ gAB conjProdWord = aJ * gJ⁻¹ * bJ * gJ := by
  rw [word_gen, gAB0, gAB1]

theorem matJ_mul' (g h : JH) : matJ (g * h) = matJ g * matJ h := Units.val_mul _ _

theorem matJ_one' : matJ (1 : JH) = 1 := Units.val_one

theorem matJ_pow' (g : JH) : ∀ e, matJ (g ^ e) = matJ g ^ e
  | 0 => by rw [pow_zero, pow_zero, matJ_one']
  | e + 1 => by rw [pow_succ, matJ_mul', matJ_pow' g e, pow_succ]

theorem eq_one_of_mat {g : JH} (h : matJ g = 1) : g = 1 := matJ_injective (h.trans matJ_one'.symm)

theorem ne_one_of_mat {g : JH} (h : matJ g ≠ 1) : g ≠ 1 := fun e => h (by rw [e, matJ_one'])

theorem orders_gen (a b : JH) (ha : matJ a = matA)
    (hb : matJ b = matB) :
    a ^ 2 = 1 ∧ a ≠ 1 ∧ b ^ 3 = 1 ∧ b ≠ 1 ∧
      (a * (a * b * b * a * b * a * b * a * b * a * b * a)⁻¹ * b *
        (a * b * b * a * b * a * b * a * b * a * b * a)) ^ 19 = 1 ∧
      a * (a * b * b * a * b * a * b * a * b * a * b * a)⁻¹ * b *
        (a * b * b * a * b * a * b * a * b * a * b * a) ≠ 1 := by
  obtain ⟨hA2, hA1, hB3, hB1, -, -, -, hGG, hX19, hX1⟩ := seed_parts
  generalize hg : a * b * b * a * b * a * b * a * b * a * b * a = g
  have hG : matJ g = toMat 5 133 (wordM (seedSel rowsA rowsB) gWord) := by
    rw [matrix_gWord, ← hg]
    simp only [matJ_mul', ha, hb]
  have hGi : matJ g⁻¹ = toMat 5 133 (wordM (seedSel rowsA rowsB) gInvWord) := by
    have e1 : matJ g * matJ g⁻¹ = 1 := by rw [← matJ_mul', mul_inv_cancel, matJ_one']
    rw [hG] at e1
    exact Matrix.right_inv_eq_right_inv e1 hGG
  have hX : matJ (a * g⁻¹ * b * g) = matA * toMat 5 133 (wordM (seedSel rowsA rowsB) gInvWord) *
      matB * toMat 5 133 (wordM (seedSel rowsA rowsB) gWord) := by
    rw [matJ_mul', matJ_mul', matJ_mul', ha, hb, hGi, hG]
  refine ⟨eq_one_of_mat (by rw [matJ_pow', ha, hA2]), ne_one_of_mat (by rw [ha]; exact hA1),
    eq_one_of_mat (by rw [matJ_pow', hb, hB3]), ne_one_of_mat (by rw [hb]; exact hB1),
    eq_one_of_mat (by rw [matJ_pow', hX, hX19]), ne_one_of_mat (by rw [hX]; exact hX1)⟩

theorem orders :
    aJ ^ 2 = 1 ∧ aJ ≠ 1 ∧ bJ ^ 3 = 1 ∧ bJ ≠ 1 ∧ (aJ * gJ⁻¹ * bJ * gJ) ^ 19 = 1 ∧
      aJ * gJ⁻¹ * bJ * gJ ≠ 1 :=
  orders_gen aJ bJ mat_aJ mat_bJ

theorem orderChecks_ok :
    orderChecks hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta) =
      true := by
  obtain ⟨a2, a1, b3, b1, x19, x1⟩ := orders
  have hw : ∀ l ∈ conjProdWord, l ≠ 0 ∧ l.natAbs ≤ 2 := by decide
  unfold orderChecks
  try dsimp only
  rw [hns_n, natTab_alpha, natTab_beta, CertificateChecks.KernelSporSch.HNIntr.pinvs2,
    pword_arrJ arrs_AB _ hw, word_X]
  simp only [List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ, ppow_arrJ,
    pisInv_arrJ, a2, b3, x19, peq_one, peq_ne_one a1, peq_ne_one b1, peq_ne_one x1, Bool.not_false,
    Bool.and_self]

end CertificateChecks.KernelSporSch.HNOrd2104

end
