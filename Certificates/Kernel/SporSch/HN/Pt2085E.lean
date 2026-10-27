module

public import Certificates.Kernel.SporSch.HN.Pt2085K
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2085

open CFSG.KC.LL.HNX CFSG.KD.HNPt2085 CFSG.KD.LgHNX CFSG.KC.LL

@[expose] noncomputable def edgeOk (l : Nat) : Bool :=
  ptsFn TX MS CM3 M (lget TIL l) (src l) (dst l) (lget EN l)

theorem ed_0 : edgeOk 0 = true ∧ edgeOk 1 = true ∧ edgeOk 2 = true := by decide +kernel
theorem ed_3 : edgeOk 3 = true ∧ edgeOk 4 = true ∧ edgeOk 5 = true := by decide +kernel

theorem neg_ed : Bool.not (ptsFn TX MS CM3 M (lget TIL 1) (src 0) (dst 0) 64) = true := by
  decide +kernel

end CertificateChecks.KernelSporSch.HNPt2085

end
