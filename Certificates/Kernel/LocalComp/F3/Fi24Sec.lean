module

public import Certificates.Data.Kernel.LocalComp.CubParts
public import Certificates.Data.CFSGNative.Filter.Fi24primeData
import Certificates.Kernel.LocalQT.Cmd
import Certificates.Kernel.LocalComp.PartsCmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.Kernel.LocalComp.CubParts
public meta import Certificates.Data.CFSGNative.Filter.Fi24primeData
public import CFSG.Certificates.Kernel.LocalQT.Steps

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LC.F3

@[expose] def fi24SecAs : CFSG.SectionRank.Native.Data :=
  CFSG.SectionRank.Native.fi24primeSec.asData

end CFSG.KD.LC.F3

end

public meta section

meta def CFSG.KD.LC.F3.fi24SecM : CFSG.SectionRank.Native.SecData :=
  CFSG.SectionRank.Native.fi24primeSec

meta def CFSG.KD.LC.F3.fi24SecE : CFSG.SectionRank.Native.Data :=
  CFSG.SectionRank.Native.fi24primeSec.extData

end

#lqt_prog_part CFSG.KD.LC.F3.Fi24Sec CFSG.KD.LC.F3.fi24SecE 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 0 1

#lqt_sr_secx CFSG.KD.LC.F3.Fi24Sec CFSG.KD.LC.F3.fi24SecM CFSG.KD.LC.F3.fi24SecAs 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2
