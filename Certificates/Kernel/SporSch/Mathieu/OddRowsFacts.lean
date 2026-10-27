module

public import Certificates.Kernel.SporSch.Mathieu.OddRowsChecks
public import Certificates.Kernel.SporSch.Mathieu.M11Facts
public import Certificates.Kernel.SporSch.Mathieu.M12Facts
public import Certificates.Kernel.SporSch.Mathieu.M22Facts
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import Certificates.Kernel.SporSch.Mathieu.M24Facts
public import CFSG.Certificates.Kernel.SporSch.OddRowsSound

public section

namespace CertificateChecks.KernelSporSch.OddRowsK

open CFSG.KS.SporSch.OddRows CFSG.OddStandard CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch

theorem facts6000 : (oddRowsCheck 11 m11CentQ1 m11Cg1 m11Primes1 m11Specs1 2000 = true)
    ∧ (oddRowsCheck 12 m12CentQ1 m12Cg1 m12Primes1 m12Specs1 2000 = true)
    ∧ (oddRowsCheck 12 m12CentQ2 m12Cg2 m12Primes2 m12Specs2 2000 = true)
    ∧ (oddRowsCheck 22 m22CentQ1 m22Cg1 m22Primes1 m22Specs1 2000 = true)
    ∧ (oddRowsCheck 23 m23CentQ1 m23Cg1 m23Primes1 m23Specs1 2000 = true)
    ∧ (oddRowsCheck 24 m24CentQ1 m24Cg1 m24Primes1 m24Specs1 2000 = true)
    ∧ (oddRowsCheck 24 m24CentQ2 m24Cg2 m24Primes2 m24Specs2 2000 = true) :=
  ⟨oddRowsCheck_of_rowsK M11OC.chainC1 (by decide) (by decide) (by norm_num) m11,
    oddRowsCheck_of_rowsK M12OC.chainC1 (by decide) (by decide) (by norm_num) m12a,
    oddRowsCheck_of_rowsK M12OC.chainC2 (by decide) (by decide) (by norm_num) m12b,
    oddRowsCheck_of_rowsK M22OC.chainC1 (by decide) (by decide) (by norm_num) m22,
    oddRowsCheck_of_rowsK M23OC.chainC1 (by decide) (by decide) (by norm_num) m23,
    oddRowsCheck_of_rowsK M24OC.chainC1 (by decide) (by decide) (by norm_num) m24a,
    oddRowsCheck_of_rowsK M24OC.chainC2 (by decide) (by decide) (by norm_num) m24b⟩

end CertificateChecks.KernelSporSch.OddRowsK

end
