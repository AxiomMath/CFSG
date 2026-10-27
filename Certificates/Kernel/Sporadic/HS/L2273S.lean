module

public import Certificates.Kernel.Sporadic.HS.L2273K
public import Certificates.Kernel.LocalQT.Tc.Gen

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HSL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def qSl (s : Nat) : Bool :=
  penumSlK 3850 12 (mask 12) (3850 * 12) false Q.G Q.GI 6 Q.cnt Q.T Q.PL Q.POS Q.SRT Q.SRI
    (Nat.mul s 8) 8

@[expose] noncomputable def dSl (s : Nat) : Bool :=
  penumSlK 3850 12 (mask 12) (3850 * 12) false D.G D.GI 2 D.cnt D.T D.PL D.POS D.SRT D.SRI
    (Nat.mul s 16) 16

@[expose] noncomputable def oSl (s : Nat) : Bool :=
  allN 7 (fun l => penumSlK 3850 12 (mask 12) (3850 * 12) true (oG l) (oGI l) 2 (oC l) (oT l)
    (oPL l) (oPOS l) (oSRT l) (oSRI l) (Nat.mul s 2) 2)

end CFSG.KD.HSL

#kqb_range CFSG.KD.HSL.QS CFSG.KD.HSL.qSl 0 8
#kqb_all CFSG.KD.HSL.QS CFSG.KD.HSL.qSl 8
#kqb_range CFSG.KD.HSL.DS CFSG.KD.HSL.dSl 0 23
#kqb_all CFSG.KD.HSL.DS CFSG.KD.HSL.dSl 23
#kqb_range CFSG.KD.HSL.OS CFSG.KD.HSL.oSl 0 45
#kqb_all CFSG.KD.HSL.OS CFSG.KD.HSL.oSl 45

end
