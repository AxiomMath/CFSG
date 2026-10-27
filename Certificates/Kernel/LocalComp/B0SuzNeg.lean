module

public import Certificates.Kernel.LocalComp.B0SuzChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.B0Suz.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.B0SuzK
open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore
open CFSG.KLie.CT (notB)
open CertificateChecks.KernelLC

theorem base_id : notB (baseK (pidn 1782 11) SuzB0Q.F SuzB0QP SuzB0QE) = true := by quickRfl

theorem rule_zero : notB (ruleK T SuzB0QP (fun _ _ => 0) 2) = true := by quickRfl

theorem dist_const : notB (distK fun _ => SuzB0QE 0) = true := by quickRfl

theorem conj_shift :
    notB (conjK T SuzB0Q.F C SuzB0QP fun k i => (Nat.xor (act k i).1 1, (act k i).2)) = true := by
  quickRfl

theorem q0_inEnum : notB (q0K T OT SuzB0Q.F SuzB0QP oact SuzB0M.N SuzB0M.T (SuzB0M.T 0)) = true := by
  quickRfl

theorem shat_noTrans : notB (shatK T C SuzB0QP typeYWord typeY'Word typeA0 polarBit
    (fun _ => 0) (fun _ => none)) = true := by quickRfl

end CertificateChecks.KernelLC.B0Suz.Neg

end
