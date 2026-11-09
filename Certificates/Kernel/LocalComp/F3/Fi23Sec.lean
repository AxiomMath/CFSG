module

public import Certificates.Data.Kernel.LocalComp.CubParts
public import Certificates.Data.CFSGNative.Filter.Fi23Data
import Certificates.Kernel.LocalQT.Cmd
import Certificates.Kernel.LocalComp.PartsCmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.Kernel.LocalComp.CubParts
public meta import Certificates.Data.CFSGNative.Filter.Fi23Data
public import CFSG.Certificates.Kernel.LocalQT.Steps

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LC.F3

@[expose] def fi23SecAs : CFSG.SectionRank.Native.Data :=
  CFSG.SectionRank.Native.fi23Sec.asData

end CFSG.KD.LC.F3

end

public meta section

meta def CFSG.KD.LC.F3.fi23SecM : CFSG.SectionRank.Native.SecData :=
  CFSG.SectionRank.Native.fi23Sec

meta def CFSG.KD.LC.F3.fi23SecE : CFSG.SectionRank.Native.Data :=
  CFSG.SectionRank.Native.fi23Sec.extData

end

#lqt_prog_part CFSG.KD.LC.F3.Fi23Sec CFSG.KD.LC.F3.fi23SecE 3 253
  CFSG.Blueprint.NativeSporadic.Fi23Seed1 CFSG.Blueprint.NativeSporadic.Fi23Seed2 0 1

#lqt_sr_secx CFSG.KD.LC.F3.Fi23Sec CFSG.KD.LC.F3.fi23SecM CFSG.KD.LC.F3.fi23SecAs 3 253
  CFSG.Blueprint.NativeSporadic.Fi23Seed1 CFSG.Blueprint.NativeSporadic.Fi23Seed2
