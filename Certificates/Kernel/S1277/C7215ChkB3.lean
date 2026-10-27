module

public import Certificates.Data.Kernel.S1277K7215
public import Certificates.Kernel.S1277.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.C7215

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.C7215 CFSG.KD.S1277Gm

theorem ok11c : ck11 gmIdx (dreps.drop 18) = true := by quickRfl

end CFSG.KP.C7215

end
