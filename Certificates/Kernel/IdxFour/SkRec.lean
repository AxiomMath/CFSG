module

public import Certificates.Kernel.IdxFour.SkData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.IF4K cf17612r0c (fun c => CFSG.KD.IF4K.blk (nat_lit 0) c) 0 16

#kc_each CFSG.KD.IF4K cf17612r1c (fun c => CFSG.KD.IF4K.blk (nat_lit 1) c) 0 1

namespace CFSG.KD.IF4K

#kc_forall_chunks cf17612r0all (fun c => blk (nat_lit 0) c = true) 16 CFSG.KD.IF4K.cf17612r0c 1

end CFSG.KD.IF4K

end
