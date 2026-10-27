module

public import Certificates.Kernel.Sporadic.Fi24Alpha.C0
public import Certificates.Kernel.Sporadic.Fi24Alpha.C1
public import Certificates.Kernel.Sporadic.Fi24Alpha.C2
public import Certificates.Kernel.Sporadic.Fi24Alpha.C3
public import Certificates.Kernel.Sporadic.Fi24Alpha.C4
public import Certificates.Kernel.Sporadic.Fi24Alpha.C5
public import Certificates.Kernel.Sporadic.Fi24Alpha.C6
public import Certificates.Kernel.Sporadic.Fi24Alpha.C7
public import Certificates.Kernel.Sporadic.Fi24Alpha.C8
public import Certificates.Kernel.Sporadic.Fi24Alpha.C9
public import Certificates.Kernel.Sporadic.Fi24Alpha.C10
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CFSG.KD.Fi24Alpha

#kc_forall_chunks chk_all (fun c => chk c = true) 110 CFSG.KD.Fi24Alpha.chk 1

end CFSG.KD.Fi24Alpha

end
