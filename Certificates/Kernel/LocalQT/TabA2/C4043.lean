module

public import Certificates.Kernel.LocalQT.TabA2.D4043
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.TA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.TabA2

theorem hd_ok : penumHdK idn S.cnt 20160 S.T S.PL = true := by quickRfl

theorem cnt_ok : Nat.beq S.cnt 20160 = true := by quickRfl

theorem gen_ok : allN 3 (fun j => cn (S.G j)) = true := by quickRfl

theorem u1_ok : u1K S.T U W S.cnt = true := by quickRfl

theorem u2_ok : u2K U = true := by quickRfl

theorem u3_ok : memU U idn = true := by quickRfl

theorem r_ok : rK U (X 2) = true := by quickRfl

theorem a0_ok : a0K S.T U (X 0) (X 2) (W 32) S.cnt = true := by quickRfl

theorem z_ok : zK S.T U (X 1) (X 2) (W 33) S.cnt = true := by quickRfl

theorem trans_ok : transK S.T U WT (X 0) S.cnt = true := by quickRfl

theorem wit_ok : witK U (X 2) = true := by quickRfl

end CFSG.KD.LQT.TA

end
