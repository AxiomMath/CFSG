module

public import Certificates.Data.Kernel.M24Dc.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.M24Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.K1.SporadicPerm

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

theorem mems : (List.range 13).all memOK = true := by
  quickRfl

theorem ots : (List.range 13).all otOK = true := by
  quickRfl

theorem tabs : tabsOK = true := by
  quickRfl

theorem invs : invOK = true := by
  quickRfl

theorem mws : mwOK = true := by
  quickRfl

theorem fix : fixOK = true := by
  quickRfl

theorem move : moveOK = true := by
  quickRfl

theorem top : topOK = true := by
  quickRfl

theorem tabsB : (J.tabs == [m24ta, m24tb, (m24SLP[180]!).toList, (m24SLP[187]!).toList,
    (m24SLP[196]!).toList, (m24SLP[211]!).toList, (m24SLP[218]!).toList, (m24SLP[223]!).toList,
    (m24SLP[228]!).toList, (m24SLP[231]!).toList]) = true := by
  quickRfl

end CFSG.KD.M24Dc

end
