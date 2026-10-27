module

public import Certificates.Kernel.IdxFour.E0Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.IF4E cf17601r1c (fun c => CFSG.KD.IF4E.blk (nat_lit 1) c) 0 18
#kc_each CFSG.KD.IF4E cf17601r2c (fun c => CFSG.KD.IF4E.blk (nat_lit 2) c) 0 2
#kc_each CFSG.KD.IF4E cf17601r3c (fun c => CFSG.KD.IF4E.blk (nat_lit 3) c) 0 1
#kc_each CFSG.KD.IF4E cf17601r4c (fun c => CFSG.KD.IF4E.blk (nat_lit 4) c) 0 1

namespace CFSG.KD.IF4E

#kc_forall_chunks cf17601r1all (fun c => blk (nat_lit 1) c = true) 18 CFSG.KD.IF4E.cf17601r1c 1
#kc_forall_chunks cf17601r2all (fun c => blk (nat_lit 2) c = true) 2 CFSG.KD.IF4E.cf17601r2c 1
#kc_forall_chunks cf17601r3all (fun c => blk (nat_lit 3) c = true) 1 CFSG.KD.IF4E.cf17601r3c 1
#kc_forall_chunks cf17601r4all (fun c => blk (nat_lit 4) c = true) 1 CFSG.KD.IF4E.cf17601r4c 1

end CFSG.KD.IF4E

end
