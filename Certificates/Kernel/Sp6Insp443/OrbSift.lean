module

public import Certificates.Kernel.Sp6Insp443.Orb
public import Certificates.Kernel.Sporadic.Co3.Sp36
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor

@[expose] noncomputable def siftL : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => bAnd(Co3Text36.hiOK c, bAnd(Co3Sp36.sift c, ih)))

@[expose] noncomputable def siftLL : List (List Nat) → Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(siftL c, ih))

theorem ch725105s : bAnd(siftL [O.X5, O.X7], bAnd(siftLL O.C5, siftLL O.C7)) = true := by
  quickRfl

end CertificateChecks.KernelS6I

end
