module

public import Certificates.Kernel.LocalQT.Lat.C4053
public import CFSG.Certificates.Kernel.LocalQTLatMSound
public import Certificates.Data.Kernel.LocalQT.LatT
public import CFSG.Certificates.Kernel.LocalQTLatESound
public import Certificates.Data.Kernel.LocalQT.ChainInj
import CFSG.Certificates.Kernel.LocalQTTleTSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M22DataInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LocalQTListLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
import CFSG.Certificates.Kernel.LocalQTLatCCheckSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4106

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
open CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def ms : List Mem := (cert.tGens :: cert.lat).map fun g => (g.map code, false, [])

theorem hs : latSixC 22 C4053.C cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)) ms
    cert.sizes ([m22AData].map fun A => (A.gens.map code, A.perf)) = true := by quickRfl

theorem ht : tleT 22 C4053.C cert.depth (cert.mGens.map code) C4053.MW 2 C4053.TW 38
    (cert.tGens.map code) = true := by
  rw [tleT, C4053.p1, C4053.p2, C4053.p8]
  rfl

end CFSG.KD.LQT.C4106

end
