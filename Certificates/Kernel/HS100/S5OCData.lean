module

public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.HS100.S5OData
public import Certificates.Data.Kernel.BfsPinBase
meta import Certificates.Kernel.HS100.S5OData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelHS100.OC CertificateChecks.KernelHS100.S5OE.gC 100 7 1680
#kss_natlist CertificateChecks.KernelHS100.OC.SKT CertificateChecks.KernelHS100.S5OE.kC

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] noncomputable def OC.SK : List Nat := (List.range 40320).map OC.SKT

@[expose] noncomputable def pw5 (a : Nat) : Nat := pm a (pm a (pm a (pm a a)))

@[expose] noncomputable def zcOne (a : Nat) : Bool :=
  !Nat.beq (pm (OX.F 4) a) (pm a (OX.F 4)) || !Nat.beq (pw5 a) (pidn 100 7) ||
    Nat.beq a (pidn 100 7)

@[expose] noncomputable def zcBlk (b : Nat) : Bool :=
  allN 1680 fun i => zcOne (OC.T (1680 * b + i))

end CertificateChecks.KernelHS100

end
