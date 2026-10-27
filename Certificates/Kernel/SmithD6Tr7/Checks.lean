module

public import Certificates.Data.Kernel.SmithD6.Tr7K

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Tr7

open CFSG.KD.SmithD6

theorem tr7Dim0_ok : tr7DimK 0 = true := by decide +kernel
theorem tr7Dim1_ok : tr7DimK 1 = true := by decide +kernel
theorem tr7Dim2_ok : tr7DimK 2 = true := by decide +kernel
theorem tr7Dim3_ok : tr7DimK 3 = true := by decide +kernel
theorem tr7Dim4_ok : tr7DimK 4 = true := by decide +kernel
theorem tr7Dim5_ok : tr7DimK 5 = true := by decide +kernel
theorem tr7Dim6_ok : tr7DimK 6 = true := by decide +kernel

theorem tr7Head0_ok : tr7HeadK 0 = true := by decide +kernel
theorem tr7Head1_ok : tr7HeadK 1 = true := by decide +kernel
theorem tr7Head2_ok : tr7HeadK 2 = true := by decide +kernel
theorem tr7Head3_ok : tr7HeadK 3 = true := by decide +kernel
theorem tr7Head4_ok : tr7HeadK 4 = true := by decide +kernel

theorem tr7Forest0_ok : tr7ForestOK 0 (tr7Dim 0) = true := by decide +kernel
theorem tr7Forest1_ok : tr7ForestOK 1 (tr7Dim 1) = true := by decide +kernel
theorem tr7Forest2_ok : tr7ForestOK 2 (tr7Dim 2) = true := by decide +kernel
theorem tr7Forest3_ok : tr7ForestOK 3 (tr7Dim 3) = true := by decide +kernel
theorem tr7Forest4_ok : tr7ForestOK 4 (tr7Dim 4) = true := by decide +kernel

end CertificateChecks.SmithD6Tr7

end
