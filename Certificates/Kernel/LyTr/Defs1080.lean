module

public import Certificates.Kernel.LyTr.Data1080

public section

namespace CertificateChecks.KernelLyTr

@[expose] noncomputable def LAB (l : Int) : Nat :=
  if l = 1 then UH.F 0 else if l = 2 then UH.F 3 else if l = -1 then UHI 0 else UHI 3

@[expose] noncomputable def LY (l : Int) : Nat :=
  if 0 < l then R1.GI (l.toNat - 1) else R1I ((-l).toNat - 1)

end CertificateChecks.KernelLyTr

end
