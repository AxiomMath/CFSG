module

public import Certificates.Kernel.IdxFour.E0Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.IF4E cf17601r0c (fun c => CFSG.KD.IF4E.blk (nat_lit 0) c) 0 36

namespace CFSG.KD.IF4E

#kc_forall_chunks cf17601r0all (fun c => blk (nat_lit 0) c = true) 36 CFSG.KD.IF4E.cf17601r0c 1

end CFSG.KD.IF4E

end
