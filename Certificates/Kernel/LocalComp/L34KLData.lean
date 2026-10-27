module

public import Certificates.Kernel.LocalComp.L34KLGen
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.L34KLGen
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelLC.L34KL.W include_bytes "data/L34KLData.W.items" 240 8093513036974851203
#kc_items CertificateChecks.KernelLC.L34KL.PA include_bytes "data/L34KLData.PA.items" 12 9681337574870170556

namespace CertificateChecks.KernelLC.L34KL

open CFSG.KLie.CT (fget)

@[expose] noncomputable def Q (j : Nat) : Nat := fget (W j) (nat_lit 0) (nat_lit 16)

@[expose] noncomputable def QS (j : Nat) : Nat := fget (W j) (nat_lit 1) (nat_lit 16)

@[expose] noncomputable def TS (j : Nat) : Nat := fget (W j) (nat_lit 2) (nat_lit 16)

end CertificateChecks.KernelLC.L34KL

end
