module

public import Certificates.Data.Kernel.SporLatOrbP
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23

set_option maxRecDepth 100000

public section

namespace CFSG.KD.E68S4212

open CFSG.KC.SLOrb CFSG.QuasithinUnique.K1.SporadicPerm

theorem tab11 : (tabOK 5 11 m11ta.toArray m11tb.toArray && ltB 11 m11SLP[159]!) = true := by
  quickRfl

theorem tab12 : (tabOK 5 12 m12ta.toArray m12tb.toArray && ltB 12 m12SLP[153]!) = true := by
  quickRfl

theorem tab22 : (tabOK 5 22 m22ta.toArray m22tb.toArray && ltB 22 m22SLP[163]!) = true := by
  quickRfl

theorem orb11 : orbChk (actS 5 11 [pk 5 11 m11ta.toArray.toList, pk 5 11 m11tb.toArray.toList]) 2
    [pz 5 11 m11SLP[159]!] 165 = true := by quickRfl

theorem orb12 : orbChk (actS 5 12 [pk 5 12 m12ta.toArray.toList, pk 5 12 m12tb.toArray.toList]) 2
    [pz 5 12 m12SLP[153]!] 495 = true := by quickRfl

theorem orb22 : orbChk (actS 5 22 [pk 5 22 m22ta.toArray.toList, pk 5 22 m22tb.toArray.toList]) 2
    [pz 5 22 m22SLP[163]!] 1155 = true := by quickRfl

end CFSG.KD.E68S4212

end
