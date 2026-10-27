module

public import Certificates.Kernel.IdxFour.OrbData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.IF4O cf17641e (fun c => CFSG.KD.IF4O.blk c) 0 32

namespace CFSG.KD.IF4O

#kc_forall_chunks cf17641all (fun c => blk c = true) 32 CFSG.KD.IF4O.cf17641e 1

theorem cf17641top : top = true := by decide +kernel

end CFSG.KD.IF4O

end
