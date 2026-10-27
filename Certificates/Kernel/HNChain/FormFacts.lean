module

public import Certificates.Kernel.HNChain.Form
public import CFSG.Sporadic.HNSchreier.Algebra
public import CFSG.Sporadic.HNSchreier.VectorData

public section

namespace CertificateChecks.KernelHNChain.Form

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.He.Native Matrix

theorem form_parts : formMᵀ = formM ∧ formM.det ≠ 0 ∧ matAᵀ * formM * matA = formM ∧
    matBᵀ * formM * matB = formM := by
  have hM : toMat 5 133 rowsM = formM := by
    rw [rowsM, toMat_rowsOf, formM_eq]
  have h := formFacts
  unfold formChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := congrArg (toMat 5 133) h1
  have e2 := congrArg (toMat 5 133) h2
  have e3 := congrArg (toMat 5 133) h3
  have e4 := congrArg (toMat 5 133) h4
  rw [toMat_colsMat_eq_transpose, hM] at e1
  rw [toMat_mulM, toMat_idM, hM] at e2
  rw [toMat_mulM, toMat_mulM, toMat_colsMat_eq_transpose, hM, toMat_rowsA] at e3
  rw [toMat_mulM, toMat_mulM, toMat_colsMat_eq_transpose, hM, toMat_rowsB] at e4
  refine ⟨e1, ?_, e3, e4⟩
  intro hdet
  have := congrArg Matrix.det e2
  rw [Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end CertificateChecks.KernelHNChain.Form

end
