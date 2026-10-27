module

public import Certificates.Data.Kernel.M24G.Orbits
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.OrbData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.SextFactsC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem ok : sextFactsF (lookW 1771 144 (packW 24) (decW 6 24) SL) (lookW 3795 72 Native.key3 dec3 TL)
    (lookW 3795 77 (packW 11) (decW 7 11) TS)
    (fun q => (maskL ((xiCls (lookW 1771 144 (packW 24) (decW 6 24) SL)).getD 1 [])).testBit q)
    (Native.uTabs.all fun g => imgSextF g.toList Native.baseSext == Native.baseSext)
    (fun cls => classOrbitK Native.nSext cls [1, 90, 240, 1440]
      (sextStepsK SL (lookW 1771 144 (packW 24) (decW 6 24) SL) Native.uTabs) xRuns)
    (fun cls => classOrbitK Native.nTrio cls [15, 180, 720, 2880]
      (trioStepsK TL (lookW 3795 72 Native.key3 dec3 TL) Native.uTabs) kRuns) = true := by
  decide +kernel

end CFSG.KC.M24G.SextFactsC
