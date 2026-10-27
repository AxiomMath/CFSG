module

public import CFSG.Sporadic.J4.QT2LocX0NNative
public import Certificates.Kernel.J4Q.QT2A
import Certificates.Kernel.J4Q.Strs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.X0S CFSG.Sporadic.J4.QT2.x0Strings

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem x0g0_eq : x0GenRows[0]! = wR (w5K X0S.s0) := by
  rw [x0GenRows, x0Words, X0S.eq]
  simp only [List.map_cons, List.map_nil, List.getElem!_toArray, List.getElem!_cons_zero, w5_ofList]

theorem x0g0_enc : WfA (x0GenRows[0]!) ∧ encR (x0GenRows[0]!) = wordJ c rm one G5 G5i (w5K X0S.s0) := by
  rw [x0g0_eq]
  exact wR_enc _

theorem nRows_enc : WfA nRows ∧ encR nRows = mulJ c rm (mulJ c rm (wordJ c rm one G5 G5i nWordU)
    (etaK c rm one Us nMask)) (wordJ c rm one G5 G5i nWordV) :=
  mul_enc hK (mul_enc hK (wR_enc nWordU) (eta_enc nMask)) (wR_enc nWordV)

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem c4014 : (chkNConj = true) := by
  unfold chkNConj
  rw [eqRows_of (mul_enc hK nRows_enc x0g0_enc) (mul_enc hK (mul_enc hK x0g0_enc x0g0_enc) nRows_enc)]
  quickRfl

end CertificateChecks.KernelJ4Q

end
