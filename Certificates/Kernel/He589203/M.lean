module

public import Certificates.Kernel.LocalQT.Base.SlpGen
public meta import Certificates.Kernel.He589203.Q
public import Certificates.Data.DcHeOverV
meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.LocalQT.Base.C4141D
public import Certificates.Data.Kernel.DcK

public section

namespace CFSG.KD.He589203

open CFSG.KC.DcK CFSG.KC.E64F CFSG.Quasithin.H13.LocDbl.HeCert

@[expose] noncomputable def im (c p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 c p

end CFSG.KD.He589203

end
