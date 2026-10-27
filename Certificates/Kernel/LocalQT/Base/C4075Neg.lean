module

public import Certificates.Data.Kernel.LocalQT.Base
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4075.Neg

open CFSG.KC.LQT.BC CFSG.QuasithinUnique.K1.SporadicPerm

theorem order :
    (baseK 11 m11ta m11tb m11Prog m11Qp 159 189 193 191 195 5 100000 64).not = true := by
  quickRfl

theorem zNode :
    (baseK 11 m11ta m11tb m11Prog m11Qp 189 189 193 191 195 4 100000 64).not = true := by
  quickRfl

theorem rounds :
    (baseK 11 m11ta m11tb m11Prog m11Qp 159 189 193 191 195 4 100000 1).not = true := by
  quickRfl

theorem oneGen :
    (baseK 11 m11ta m11tb m11Prog (m11Qp.take 1) 159 189 193 191 195 4 100000 64).not = true := by
  quickRfl

end CFSG.KD.LQT.C4075.Neg

end
