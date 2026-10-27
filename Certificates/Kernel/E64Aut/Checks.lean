module

public import Certificates.Data.Kernel.E64AutK
public import Certificates.Kernel.WrTwin.E64Checks

public noncomputable section

namespace CFSG.KD.E64Aut

open CFSG.KC.WrTwin CFSG.KC.E64AutK CFSG.KD.WrTwin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117 Certificates.E64Aut

@[expose] def e14 : Nat := enc (1 : Wr 7)

@[expose] def pi14 : Nat := enc (allOnes 7)

@[expose] def P168 : List (Nat × Nat) := prods e14 (chain64.map (·.map lvl))

@[expose] def CG0 : List Nat := (C8 ()).map fun c => enc (c * g0 () * c⁻¹)

@[expose] def stepOK (p : (Fin 7 × Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7 × Fin 7)) :
    Bool :=
  conjIn pi14 (lvl rho).1 (lvl rho).2 ((twinQ p.1).map enc) ((twinQ p.2).map enc)

theorem e64a_cent : centOK e14 pi14 P168 V64 ((S0 ()).map enc) = true := by decide +kernel

theorem e64a_sol : solOK e14 pi14 relsK P168 V64 (tab (W0 ())) CG0 = true := by decide +kernel

theorem e64a_mem : memOK e14 pi14 (tab (S0 ())) (membersQ.map enc) = true := by decide +kernel

theorem e64a_step : quadSteps.all stepOK = true := by decide +kernel

theorem e64a_facts : ((S0 ()).all inM && (C8 ()).all inM && inM (ofPerm rho) &&
    decide (ofPerm rho ^ 7 = 1) && (W0 ()).all (fun s => decide (s ∈ twinQ (2, 4, 5, 6))) &&
    rels.all (fun r => inPiP e14 pi14 (pw e14 (tab (S0 ())) r)) &&
    ((C8 ()).all fun c => decide (c * c = 1) && (W0 ()).all fun s => decide (c * s = s * c)) &&
    relsK.all (fun r => decide (r ∈ rels))) = true := by
  decide +kernel

end CFSG.KD.E64Aut

end
