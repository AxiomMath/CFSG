module

public import Certificates.Kernel.LocalComp.L34Idx.Gen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.L34Idx.Gen
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelLC.L34IX.Y include_bytes "data/Data.Y.items" 1728 13676709374303804014
#kc_items CertificateChecks.KernelLC.L34IX.WP include_bytes "data/Data.WP.items" 4412 17650356858489129082
#kc_items CertificateChecks.KernelLC.L34IX.TSP include_bytes "data/Data.TSP.items" 144 12067163740133679657

namespace CertificateChecks.KernelLC.L34IX

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (fget)

@[expose] noncomputable def YI (q : Nat) : Nat := pinvS 42 6 (mask 6) (Y q)

@[expose] noncomputable def W (k : Nat) : Nat :=
  fget (WP (Nat.shiftRight k (nat_lit 4))) (Nat.land k (nat_lit 15)) (nat_lit 16)

@[expose] noncomputable def TS (i : Nat) : Nat :=
  fget (TSP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 16)

end CertificateChecks.KernelLC.L34IX

end
