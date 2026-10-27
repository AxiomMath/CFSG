module

public import CFSG.Certificates.Kernel.M24G.StepsSound
public import CFSG.Certificates.Kernel.M24G.BfsReplaySound
public import Certificates.Kernel.M24G.SextReplay
public import Certificates.Kernel.M24G.TrioReplay

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem trioData_eq : Native.trioData () = (TL.toArray, tPar.toArray, tGen.toArray) := by
  change Native.bfs Native.key3 (Native.genTabs.map Native.imgTrio) Native.baseTrio 5000 = _
  rw [trioSteps_eq]
  exact bfs_eq_of_replayOK trioReplay_ok

theorem sextData_eq : Native.sextData () = (SL.toArray, sPar.toArray, sGen.toArray) := by
  change Native.bfs Native.keyL (Native.genTabs.map Native.imgSext) Native.baseSext 3000 = _
  rw [sextSteps_eq]
  exact bfs_eq_of_replayOK sextReplay_ok

theorem trioList_eq : Native.trioList () = TL.toArray := by
  rw [Native.trioList, trioData_eq]

theorem sextList_eq : Native.sextList () = SL.toArray := by
  rw [Native.sextList, sextData_eq]

end CFSG.KC.M24G
