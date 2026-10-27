module

public import Certificates.Data.Kernel.LocalComp.CubParts
public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import Certificates.Kernel.LocalQT.Cmd
import Certificates.Kernel.LocalComp.PartsCmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.Kernel.LocalComp.CubParts
public meta import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
public import CFSG.Certificates.Kernel.LocalQT.Steps

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LC.F3

@[expose] def fi24SevenAs : CFSG.SectionRank.Native.Data :=
  (CFSG.SectionRank.Native.fi24MultSeven ()).asData

end CFSG.KD.LC.F3

end

public meta section

meta def CFSG.KD.LC.F3.fi24SevenM : CFSG.SectionRank.Native.CubData :=
  CFSG.SectionRank.Native.fi24MultSeven ()

meta def CFSG.KD.LC.F3.fi24SevenE : CFSG.SectionRank.Native.Data :=
  (CFSG.SectionRank.Native.fi24MultSeven ()).extData

end

#lqt_prog_part CFSG.KD.LC.F3.Fi24Seven CFSG.KD.LC.F3.fi24SevenE 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 0 1

#lqt_sr_cubx CFSG.KD.LC.F3.Fi24Seven CFSG.KD.LC.F3.fi24SevenM CFSG.KD.LC.F3.fi24SevenAs 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2
