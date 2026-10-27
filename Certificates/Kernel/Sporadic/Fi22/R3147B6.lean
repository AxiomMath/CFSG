
module

public import Certificates.Kernel.Sporadic.Fi22.R3147B6D
public import Certificates.Kernel.Sporadic.Fi22.R3147B7
public import CFSG.Certificates.Kernel.Spor.RawTreeTrunc
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22R6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem lrOK : allN 6 (fun l => Nat.beq (Fi22R6.LR l) (Fi22R7.LR l)) = true := by quickRfl
theorem stOK : allN 6 (fun l => Nat.beq (Fi22R6.ST l) (Fi22R7.ST l)) = true := by quickRfl
theorem bpOK : allN 6 (fun t => Nat.beq (pg 12 (mask 12) Fi22R7.BP t) (pg 12 (mask 12) Fi22R6.BP t)) =
    true := by quickRfl

theorem hs : SchBOK 3510 12 6 Fi22R6.S Fi22R6.SI Fi22R6.LR Fi22R6.ST 19 Fi22R6.BP :=
  Orb.schBOK_trunc (by decide) Fi22R7.hs rfl rfl
    (fun l hl => Nat.eq_of_beq_eq_true (allN_spec lrOK l hl))
    (fun l hl => Nat.eq_of_beq_eq_true (allN_spec stOK l hl))
    (fun t ht => Nat.eq_of_beq_eq_true (allN_spec bpOK t ht))

end CertificateChecks.KernelSpor.Fi22R6

end
