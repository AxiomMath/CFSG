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

@[expose] noncomputable def rowF (i : Nat) : Bool := rowOK INV CML PTL PTP PP TT WALL i

#kc_each rowF 0 191

#kc_forall_chunks rows_ok (fun k => rowF k = true) 191 CertificateChecks.KernelJ4Fam.rowF 1

theorem neg_row : notB (rowOK INV (CML.set 5 (CML.getD 5 0 ^^^ 1)) PTL PTP PP TT WALL 5) = true := by
  quickRfl

end CertificateChecks.KernelJ4Fam
