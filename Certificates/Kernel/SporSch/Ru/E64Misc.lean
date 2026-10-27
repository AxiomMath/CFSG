module

public import Certificates.Kernel.SporSch.Ru.E64K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuE64

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.RuE64 CertificateChecks.KernelSporSch.RuE64D
open CFSG.KLie.CT (bit popc)

theorem codesOK : (List.range 687).map cd = (List.range 16384).filter (invK LR TR) := by
  decide +kernel

theorem cdLt : allN 687 (fun i => Nat.blt (cd i) 16384) = true := by quickRfl

theorem degC : allN 687 (fun i => Nat.beq (deg i) (popc 687 (K i))) = true := by quickRfl

theorem ub0 : ubC 0 = true := by quickRfl
theorem ub1 : ubC 1 = true := by quickRfl
theorem ub2 : ubC 2 = true := by quickRfl
theorem ub3 : ubC 3 = true := by quickRfl

theorem w0 : wC 0 = true := by quickRfl
theorem w1 : wC 1 = true := by quickRfl
theorem w2 : wC 2 = true := by quickRfl
theorem w3 : wC 3 = true := by quickRfl

theorem fin : e64K 687 K deg W = true := by quickRfl

theorem neg : bAnd(bIf(allN 687 fun j => eqB (bit (Nat.xor (R 0) 1) j) (comK LR TR (cd 0) (cd j)),
      false, true),
    bAnd(bIf(allN 687 fun j => eqB (bit (Nat.xor (K 0) 1) j) (keepK 687 R 0 j), false, true),
    bAnd(bIf(allN 687 fun i => eqB (bit (Nat.xor (W 0) 1) i) (inWK LR TR (ub 0) (cd i)),
      false, true),
    bAnd(bIf(Nat.beq (deg 0 + 1) (popc 687 (K 0)), false, true), bIf(invK LR TR 0, false, true))))) =
    true := by
  quickRfl

end CertificateChecks.KernelSporSch.RuE64

end
