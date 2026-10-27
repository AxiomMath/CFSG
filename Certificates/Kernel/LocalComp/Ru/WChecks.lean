module

public import Certificates.Kernel.LocalComp.Ru.WData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelLC.RuW

open CFSG.KC.Enum CFSG.KS CFSG.KC.LocalComp.ThreeWP

theorem kQ : Nat.beq (TQY 0) (ppow 4060 12 (mask 12) (pidn 4060 12) (wordP 4060 12 letP qW) 60) =
    true := by quickRfl

theorem kY : Nat.beq (TQY 1) (ppow 4060 12 (mask 12) (pidn 4060 12) (wordP 4060 12 letP yW) 2) =
    true := by quickRfl

theorem kHead : headWP 4060 12 TE 30 (TQY 0) (TQY 1) 1 = true := by quickRfl

@[expose] noncomputable def rowC (j : Nat) : Bool := rowWP 4060 12 gP giP 2 TE TR 30 j

@[expose] noncomputable def commC (i : Nat) : Bool := commWP 4060 12 TE i

end CertificateChecks.KernelLC.RuW

#kc_each CertificateChecks.KernelLC.RuW.rowC 0 30
#kc_each CertificateChecks.KernelLC.RuW.commC 0 30

namespace CertificateChecks.KernelLC.RuW

#kc_forall_chunks kRowC (fun j => rowC j = true) 30 CertificateChecks.KernelLC.RuW.rowC 1
#kc_forall_chunks kCommC (fun i => commC i = true) 30 CertificateChecks.KernelLC.RuW.commC 1

open CFSG.KC.LocalComp.ThreeWP in
theorem kRows : ∀ j < 30, rowWP 4060 12 gP giP 2 TE TR 30 j = true := kRowC

open CFSG.KC.LocalComp.ThreeWP in
theorem kComm : ∀ i < 30, commWP 4060 12 TE i = true := kCommC

end CertificateChecks.KernelLC.RuW
