module

public import Certificates.Data.Kernel.LocalQT.Base
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4075

open CFSG.KC.LQT.BC CFSG.QuasithinUnique.K1.SporadicPerm

theorem v11 : slpValidAux m11Prog 2 = true := by quickRfl
theorem v12 : slpValidAux m12Prog 2 = true := by quickRfl
theorem v22 : slpValidAux m22Prog 2 = true := by quickRfl
theorem v23 : slpValidAux m23Prog 2 = true := by quickRfl
theorem v24 : slpValidAux m24Prog 2 = true := by quickRfl

theorem b11 : baseK 11 m11ta m11tb m11Prog m11Qp 159 189 193 191 195 4 100000 64 = true := by
  quickRfl
theorem b12 : baseK 12 m12ta m12tb m12Prog m12Qp 153 204 208 206 210 6 100000 64 = true := by
  quickRfl
theorem b22 : baseK 22 m22ta m22tb m22Prog m22Qp 163 205 209 207 211 7 100000 64 = true := by
  quickRfl
theorem b23 : baseK 23 m23ta m23tb m23Prog m23Qp 159 199 203 201 205 7 100000 64 = true := by
  quickRfl
theorem b24 : baseK 24 m24ta m24tb m24Prog m24Qp 162 213 216 214 217 10 100000 64 = true := by
  quickRfl

end CFSG.KD.LQT.C4075

end
