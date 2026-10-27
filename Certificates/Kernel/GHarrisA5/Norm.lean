module

public import Certificates.Data.GHarrisA5Data

public section

namespace CertificateChecks.KernelGHarrisA5

open CFSG.ComponentClassification.GHarris

abbrev NormOK (a b : GL42.V4c) : Prop :=
  ∀ c ∈ GL42.V4c.all, ∀ d ∈ GL42.V4c.all, GL42.NoFiveSeven ⟨a, b, c, d⟩

theorem n00 : NormOK ⟨0, 0, 0, 0⟩ ⟨0, 0, 0, 0⟩ := by decide +kernel
theorem n01 : NormOK ⟨0, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩ := by decide +kernel
theorem n02 : NormOK ⟨0, 0, 0, 0⟩ ⟨0, 1, 0, 0⟩ := by decide +kernel
theorem n03 : NormOK ⟨0, 0, 0, 0⟩ ⟨1, 1, 0, 0⟩ := by decide +kernel
theorem n10 : NormOK ⟨1, 0, 0, 0⟩ ⟨0, 0, 0, 0⟩ := by decide +kernel
theorem n11 : NormOK ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩ := by decide +kernel
theorem n12 : NormOK ⟨1, 0, 0, 0⟩ ⟨0, 1, 0, 0⟩ := by decide +kernel
theorem n13 : NormOK ⟨1, 0, 0, 0⟩ ⟨1, 1, 0, 0⟩ := by decide +kernel
theorem n20 : NormOK ⟨0, 1, 0, 0⟩ ⟨0, 0, 0, 0⟩ := by decide +kernel
theorem n21 : NormOK ⟨0, 1, 0, 0⟩ ⟨1, 0, 0, 0⟩ := by decide +kernel
theorem n22 : NormOK ⟨0, 1, 0, 0⟩ ⟨0, 1, 0, 0⟩ := by decide +kernel
theorem n23 : NormOK ⟨0, 1, 0, 0⟩ ⟨1, 1, 0, 0⟩ := by decide +kernel
theorem n30 : NormOK ⟨1, 1, 0, 0⟩ ⟨0, 0, 0, 0⟩ := by decide +kernel
theorem n31 : NormOK ⟨1, 1, 0, 0⟩ ⟨1, 0, 0, 0⟩ := by decide +kernel
theorem n32 : NormOK ⟨1, 1, 0, 0⟩ ⟨0, 1, 0, 0⟩ := by decide +kernel
theorem n33 : NormOK ⟨1, 1, 0, 0⟩ ⟨1, 1, 0, 0⟩ := by decide +kernel

theorem norm_ok : ∀ a ∈ GL42.rowsW, ∀ b ∈ GL42.rowsW, NormOK a b := by
  intro a ha b hb
  simp only [GL42.rowsW, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  exacts [n00, n01, n02, n03, n10, n11, n12, n13, n20, n21, n22, n23, n30, n31, n32, n33]

end CertificateChecks.KernelGHarrisA5

end
