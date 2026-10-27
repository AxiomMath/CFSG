module

public import Certificates.Data.Kernel.Foote82StabK
public import Certificates.Kernel.OmegaEight.Chains3002

public section

set_option maxRecDepth 400000

namespace CFSG.KC.StabT919

open CFSG.KC.Census (at' pset)
open CFSG.EvenSmallLie.OmegaEightMinus (stabIdx)

@[expose] noncomputable def S0 (j x : Nat) : Nat :=
  bif decide (j < 18) && decide (x < 136) then at' 8 (CertificateChecks.KernelO8.OmM.S j) x else 0

@[expose] noncomputable def G0 (l x : Nat) : Nat := S0 (stabIdx.getD l 0) x

theorem ch919ok : (stabTreeK G0).ok = true := by decide +kernel

theorem ch919chk : stabTreeOKP S0 (stabTreeK G0).P (stabTreeK G0).L (stabTreeK G0).D
    (stabTreeK G0).C ((stabTreeK G0).R.getD 0 0) ((stabTreeK G0).R.getD 1 0) = true := by
  decide +kernel

theorem ch919dInit : (List.range 136).all (fun i => at' 16 dInit i == 1000) = true := by
  decide +kernel

end CFSG.KC.StabT919
