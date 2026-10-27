module

public import Certificates.Data.Kernel.F4M3B

public section

set_option profiler true
set_option profiler.threshold 500

namespace CFSG.KC.F4M3B

theorem ch7052 : chkN 18 = true := by decide +kernel

theorem ch7052_neg : (frc (Nat.sub (Nat.pow 2 (Nat.pow 2 18)) 1) fun t =>
    plnK 18 fun P => Nat.beq (mulK (natOps t) P P fun A2 => mulK (natOps t) A2 P fun A3 =>
      mulK (natOps t) A3 A2 fun A5 => mulK (natOps t) A5 A5 fun A10 =>
        mulK (natOps t) A10 A5 fun A15 =>
          bor (natOps t) (bnot (natOps t) (isOne (natOps t) (detL (natOps t) P)
            (detH (natOps t) P))) (bnot (natOps t) (scal (natOps t) A15))) t) = false := by
  decide +kernel

end CFSG.KC.F4M3B

end
