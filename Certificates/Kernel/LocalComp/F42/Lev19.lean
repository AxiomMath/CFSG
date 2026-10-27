module

public import Certificates.Kernel.LocalComp.F42.P19_0
public import Certificates.Kernel.LocalComp.F42.P19_1
public import Certificates.Kernel.LocalComp.F42.P19_2
public import Certificates.Kernel.LocalComp.BlockJoin

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42 CFSG.KC.Co3Bfs CFSG.KS.Raw

theorem Lev19 : ∀ t < 36352, chk19 t = true := by
  have h0 : ∀ t < 0, chk19 t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 19838) h0 cchk19_0
  have h2 := cover_append (a := 19838) (b := 12685) h1 cchk19_1
  have h3 := cover_append (a := 32523) (b := 3829) h2 cchk19_2
  exact h3

end CertificateChecks.KernelLC.F42

end
