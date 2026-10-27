module

public import Certificates.Data.Kernel.M24G.Orbits
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.TSData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.LookC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem tl : lookOK 3795 72 Native.key3 dec3 TL = true := by decide +kernel

theorem sl : lookOK 1771 144 (packW 24) (decW 6 24) SL = true := by decide +kernel

theorem ts : lookOK 3795 77 (packW 11) (decW 7 11) TS = true := by decide +kernel

end CFSG.KC.M24G.LookC
