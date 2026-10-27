module

public import Certificates.Kernel.OmegaEight.Pi416101Q0
public import Certificates.Kernel.OmegaEight.Pi416101Q1
public import Certificates.Kernel.OmegaEight.Pi416101Q2
public import Certificates.Kernel.OmegaEight.Pi416101Q3
public import Certificates.Kernel.OmegaEight.Pi416101Q4
public import Certificates.Kernel.OmegaEight.Pi416101Q5
public import Certificates.Kernel.OmegaEight.Pi416101Q6
public import Certificates.Kernel.OmegaEight.Pi416101Q7

public section

namespace CertificateChecks.KernelO8

theorem q8_chunks : ∀ i < 8, q8Part i = true := by
  intro i hi
  interval_cases i
  · exact q8Part0
  · exact q8Part1
  · exact q8Part2
  · exact q8Part3
  · exact q8Part4
  · exact q8Part5
  · exact q8Part6
  · exact q8Part7

end CertificateChecks.KernelO8

end
