module

public import Certificates.Kernel.J4Fam.Data
public import Certificates.Data.Kernel.J4Fam
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Fam

open CFSG.KC.J4Fam
open CFSG.KC (notB)

@[expose] noncomputable def fixF (i : Nat) : Bool := fixRowOK INV FB FLL PL i

#kc_each fixF 0 191

#kc_forall_chunks fix_ok (fun k => fixF k = true) 191 CertificateChecks.KernelJ4Fam.fixF 1

theorem neg_fix : notB (fixRowOK INV (FB.set 7 (FB.getD 7 0 ^^^ 2)) FLL PL 7) = true := by quickRfl

end CertificateChecks.KernelJ4Fam
