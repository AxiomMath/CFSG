module

public import Certificates.Kernel.LocalComp.F42.P21_0
public import Certificates.Kernel.LocalComp.F42.P21_1
public import Certificates.Kernel.LocalComp.F42.P21_2
public import Certificates.Kernel.LocalComp.F42.P21_3
public import Certificates.Kernel.LocalComp.F42.P21_4
public import Certificates.Kernel.LocalComp.BlockJoin

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42 CFSG.KC.Co3Bfs CFSG.KS.Raw

theorem Lev21 : ∀ t < 66048, chk21 t = true := by
  have h0 : ∀ t < 0, chk21 t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 23707) h0 cchk21_0
  have h2 := cover_append (a := 23707) (b := 16387) h1 cchk21_1
  have h3 := cover_append (a := 40094) (b := 11380) h2 cchk21_2
  have h4 := cover_append (a := 51474) (b := 12032) h3 cchk21_3
  have h5 := cover_append (a := 63506) (b := 2542) h4 cchk21_4
  exact h5

end CertificateChecks.KernelLC.F42

end
