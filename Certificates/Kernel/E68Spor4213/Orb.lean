module

public import Certificates.Data.Kernel.SporLatOrbP
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23

set_option maxRecDepth 100000

public section

namespace CFSG.KD.E68S4213

open CFSG.KC.SLOrb CFSG.QuasithinUnique.K1.SporadicPerm

theorem tab23 : (tabOK 5 23 m23ta.toArray m23tb.toArray && ltB 23 m23SLP[159]!) = true := by
  quickRfl

theorem tab24 : (tabOK 5 24 m24ta.toArray m24tb.toArray && ltB 24 m24SLP[162]!) = true := by
  quickRfl

theorem orb23 : orbChk (actS 5 23 [pk 5 23 m23ta.toArray.toList, pk 5 23 m23tb.toArray.toList]) 2
    [pz 5 23 m23SLP[159]!] 3795 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem orb24 : orbChk (actS 5 24 [pk 5 24 m24ta.toArray.toList, pk 5 24 m24tb.toArray.toList]) 2
    [pz 5 24 m24SLP[162]!] 11385 = true := by quickRfl

end CFSG.KD.E68S4213

end
