module

public import Certificates.Kernel.LocalComp.L34NGen
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.L34NGen
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelLC.L34N.JP include_bytes "data/L34NData.JP.items" 25192 8205188666816525613
#kc_items CertificateChecks.KernelLC.L34N.C include_bytes "data/L34NData.C.items" 1082 7090619071481271612
#kc_items CertificateChecks.KernelLC.L34N.K include_bytes "data/L34NData.K.items" 432 6845397442775969061

namespace CertificateChecks.KernelLC.L34N

@[expose] noncomputable def J (q : Nat) : Nat := L34X.at16 JP (nat_lit 24) q

@[expose] noncomputable def AP (j : Nat) : Nat := K (Nat.add (nat_lit 3) j)

end CertificateChecks.KernelLC.L34N

end
