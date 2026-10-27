module

public import Certificates.Data.Kernel.M24G.StmtB
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.StmtBC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem trio_lt : TL.all (fun t => (Native.octsT t).all (· < 2 ^ 24)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem s310 : stmt310K TL TS SL = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem s313 : stmt313K TL TS SL = true := by decide +kernel

end CFSG.KC.M24G.StmtBC
