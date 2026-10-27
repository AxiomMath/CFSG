module

public import CFSG.Certificates.Kernel.LocalQTSecSound
public import Certificates.Data.Kernel.LocalComp.ReplayWit
public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import Certificates.Kernel.LocalQT.Cmd
import Certificates.Kernel.LocalComp.ReplayCmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.Kernel.LocalComp.ReplayWit
public meta import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
public import CFSG.Open.Defs
public import Certificates.Data.Kernel.LocalComp.Replay

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LC.F3

@[expose] def fi24FiveAs : CFSG.SectionRank.Native.Data :=
  (CFSG.SectionRank.Native.fi24MultFive ()).asData

end CFSG.KD.LC.F3

end

public meta section

meta def CFSG.KD.LC.F3.fi24FiveM : CFSG.SectionRank.Native.SqData :=
  CFSG.SectionRank.Native.fi24MultFive ()

meta def CFSG.KD.LC.F3.fi24FiveAsM : CFSG.SectionRank.Native.Data :=
  (CFSG.SectionRank.Native.fi24MultFive ()).asData

end

#lqt_sr_sq CFSG.KD.LC.F3.Fi24Five CFSG.KD.LC.F3.fi24FiveM 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2

#lqt_sr_replay CFSG.KD.LC.F3.Fi24Five CFSG.KD.LC.F3.fi24FiveAsM CFSG.KD.LC.F3.fi24FiveAs
