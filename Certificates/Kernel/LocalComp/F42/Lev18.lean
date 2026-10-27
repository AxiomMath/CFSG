module

public import Certificates.Kernel.LocalComp.F42.P18_0
public import Certificates.Kernel.LocalComp.F42.P18_1
public import Certificates.Kernel.LocalComp.BlockJoin

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42 CFSG.KC.Co3Bfs CFSG.KS.Raw

theorem Lev18 : ∀ t < 22016, chk18 t = true := by
  have h0 : ∀ t < 0, chk18 t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 17790) h0 cchk18_0
  have h2 := cover_append (a := 17790) (b := 4226) h1 cchk18_1
  exact h2

end CertificateChecks.KernelLC.F42

end
