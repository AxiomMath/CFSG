module

public import Certificates.Kernel.LocalComp.F42.P20_0
public import Certificates.Kernel.LocalComp.F42.P20_1
public import Certificates.Kernel.LocalComp.F42.P20_2
public import Certificates.Kernel.LocalComp.BlockJoin

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42 CFSG.KC.Co3Bfs CFSG.KS.Raw

theorem Lev20 : ∀ t < 43520, chk20 t = true := by
  have h0 : ∀ t < 0, chk20 t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 21309) h0 cchk20_0
  have h2 := cover_append (a := 21309) (b := 13795) h1 cchk20_1
  have h3 := cover_append (a := 35104) (b := 8416) h2 cchk20_2
  exact h3

end CertificateChecks.KernelLC.F42

end
