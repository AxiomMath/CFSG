module

public import Certificates.Data.Kernel.LocalComp.CubParts
public import Certificates.Data.CFSGNative.CTP.Fi24Sylow7
import Certificates.Kernel.LocalQT.Cmd
import Certificates.Kernel.LocalComp.PartsCmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.Kernel.LocalComp.CubParts
public meta import Certificates.Data.CFSGNative.CTP.Fi24Sylow7
public import CFSG.Certificates.Kernel.LocalQT.Steps

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LC.F3

@[expose] def fi24Sylow7As : CFSG.SectionRank.Native.Data :=
  CFSG.SectionRank.Native.fi24Sylow7Data.asData

end CFSG.KD.LC.F3

end

public meta section

meta def CFSG.KD.LC.F3.fi24Sylow7M : CFSG.SectionRank.Native.CubData :=
  CFSG.SectionRank.Native.fi24Sylow7Data

meta def CFSG.KD.LC.F3.fi24Sylow7E : CFSG.SectionRank.Native.Data :=
  CFSG.SectionRank.Native.fi24Sylow7Data.extData

end

#lqt_prog_part CFSG.KD.LC.F3.Fi24Sylow7 CFSG.KD.LC.F3.fi24Sylow7E 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 0 1

#lqt_sr_cubx CFSG.KD.LC.F3.Fi24Sylow7 CFSG.KD.LC.F3.fi24Sylow7M CFSG.KD.LC.F3.fi24Sylow7As 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2
