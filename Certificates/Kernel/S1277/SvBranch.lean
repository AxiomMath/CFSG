module

public import CFSG.Certificates.Kernel.S1277KArithSound
public import CFSG.Certificates.Kernel.S1277KVlSound
public import Certificates.Kernel.S1277.FrData
public import Certificates.Kernel.S1277.LatData
public import Certificates.Kernel.S1277.ModData
public import Certificates.Kernel.S1277.SvData
public import Certificates.Kernel.S1277.VlData

public section

namespace CFSG.KP.S1277Sv

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sv CFSG.KC.S1277Sig CFSG.KC.S1277Fr
  CFSG.KC.S1277Vl CFSG.KD.S1277Fr CFSG.KD.S1277Sv CFSG.KD.S1277Lat CFSG.KD.S1277Mod
  CFSG.KD.S1277Vl CFSG.KS.S1277Lat CFSG.KS.S1277Sig CFSG.KS.S1277Sv CFSG.KS.S1277Fr
  CFSG.KS.S1277Vl CFSG.KS.S1277Ar CFSG.KS.S1277Cand CFSG.Quasithin.H13.I1277 CFSG.Open
  Certificates.Data.S1277Sig

theorem sv_idx : sgin.length = 6 ∧ sgdn.getD 4 0 = 6 ∧ nmn.length = 18 := by decide +kernel

end CFSG.KP.S1277Sv

end
