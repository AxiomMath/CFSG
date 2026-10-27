module

public import Certificates.Kernel.TwoHSLe4.SO5D

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

theorem p0_eq : pgP0Code = P0L.map unpk := by decide +kernel

theorem s0_eq : pgS0Code = S0L.map unpk := by decide +kernel

theorem cj_eq : pgConjCode = CJL.map fun e => (unpk e.1, unpk e.2.1, ⟨e.2.2 % 4, Nat.mod_lt _ (by norm_num)⟩) := by
  decide +kernel

theorem sg_eq : pgTau1C = unpk (SG 0) ∧ pgTau2C = unpk (SG 1) ∧ pgTau3C = unpk (SG 2) ∧
    pgTau4C = unpk (SG 3) ∧ pgX15C = unpk (SG 4) ∧ pgX13C = unpk (SG 5) ∧ pgR0C = unpk (SG 6) ∧
    pgSf0C = unpk (SG 7) ∧ pgS1C = unpk (SG 8) := by
  decide +kernel

end CertificateChecks.KernelTwoHSLe4.SO5

end
