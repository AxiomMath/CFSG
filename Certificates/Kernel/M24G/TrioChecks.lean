module

public import Certificates.Data.Kernel.M24G.ListChecks
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.OctData

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.TrioC

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem length : TL.length = 3795 := by decide +kernel

theorem items : TL.all trioItem = true := by decide +kernel

theorem count : disjCount OctD.O = 6 * 3795 := by decide +kernel

end CFSG.KC.M24G.TrioC
