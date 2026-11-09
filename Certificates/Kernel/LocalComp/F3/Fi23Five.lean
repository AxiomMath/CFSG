module

public import CFSG.Certificates.Kernel.LocalQTSecSound
public import Certificates.Data.Kernel.LocalComp.ReplayWit
public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import Certificates.Kernel.LocalQT.Cmd
import CFSG.Certificates.Kernel.LocalQT.StepsF3Sound
import Certificates.Kernel.LocalComp.ReplayCmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.Kernel.LocalComp.ReplayWit
public meta import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
public import CFSG.Open.Defs
public import Certificates.Data.Kernel.LocalComp.Replay

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LC.F3

@[expose] def fi23FiveAs : CFSG.SectionRank.Native.Data :=
  (CFSG.SectionRank.Native.fi23MultFive ()).asData

end CFSG.KD.LC.F3

end

public meta section

meta def CFSG.KD.LC.F3.fi23FiveM : CFSG.SectionRank.Native.SqData :=
  CFSG.SectionRank.Native.fi23MultFive ()

meta def CFSG.KD.LC.F3.fi23FiveAsM : CFSG.SectionRank.Native.Data :=
  (CFSG.SectionRank.Native.fi23MultFive ()).asData

end

#lqt_sr_sq CFSG.KD.LC.F3.Fi23Five CFSG.KD.LC.F3.fi23FiveM 3 253
  CFSG.Blueprint.NativeSporadic.Fi23Seed1 CFSG.Blueprint.NativeSporadic.Fi23Seed2

#lqt_sr_replay CFSG.KD.LC.F3.Fi23Five CFSG.KD.LC.F3.fi23FiveAsM CFSG.KD.LC.F3.fi23FiveAs
