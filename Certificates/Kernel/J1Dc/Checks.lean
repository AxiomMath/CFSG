module

public import Certificates.Kernel.J1Dc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Quasithin.Background.A312SporJ1Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.J1Dc

open CFSG.KC.SLDc CFSG.Quasithin.A312S.J1

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

theorem sepB : (D.sep == List.range 1540) = true := by
  quickRfl

theorem normB : normOK = true := by
  quickRfl

theorem centB : j1CentWords.all centOK = true := by
  quickRfl

theorem sClosedB : sClosedOK = true := by
  quickRfl

theorem sDistinctB : sDistinctOK = true := by
  quickRfl

theorem sInvB : sInvOK = true := by
  quickRfl

theorem rangeB : rangeOK = true := by
  quickRfl

end CFSG.KD.J1Dc

#kss_each CFSG.KD.J1Dc.M CFSG.KD.J1Dc.memOK 17

end
