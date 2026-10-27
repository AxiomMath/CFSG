module

public import Certificates.Kernel.LocalComp.F42.P17_0
public import Certificates.Kernel.LocalComp.F42.P17_1
public import Certificates.Kernel.LocalComp.BlockJoin

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42 CFSG.KC.Co3Bfs CFSG.KS.Raw

theorem Lev17 : ∀ t < 16896, chk17 t = true := by
  have h0 : ∀ t < 0, chk17 t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 16572) h0 cchk17_0
  have h2 := cover_append (a := 16572) (b := 324) h1 cchk17_1
  exact h2

end CertificateChecks.KernelLC.F42

end
