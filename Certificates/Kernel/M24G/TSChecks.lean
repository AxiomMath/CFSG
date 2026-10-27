module

public import Certificates.Data.Kernel.M24G.TrioSexts
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.TSC

open CFSG.KC.M24G

theorem rows : tsRowsOK TL SL TS = true := by decide +kernel

end CFSG.KC.M24G.TSC
