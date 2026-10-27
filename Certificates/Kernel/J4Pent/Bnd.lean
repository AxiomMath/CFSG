module

public import Certificates.Kernel.J4Pent.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Pent

open CFSG.KC.J4Pent CFSG.KD.J4Pent CFSG.KC.J4Q CFSG.QuasithinUnique.A5

theorem bnd_ok : bAnd(allB (fun p => bAnd(Nat.blt p.1 NL, Nat.blt p.2 6720)) FXL,
    bAnd(allB (fun p => Nat.blt p.2 6720) WD,
      allB (fun j => Nat.beq (nthL 0 D4 j) (v2N (d4Reps[j]!))) (List.range 30))) = true := by
  quickRfl

end CertificateChecks.KernelJ4Pent

end
