module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import Certificates.Data.Kernel.ONanSmall.P43Gen
public import Certificates.Data.P43Twin
public import Certificates.Kernel.ONanSmall.Data.P43T

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.P43T

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.ComponentClassification.CatFactsSmall CFSG.KD.ONS.P43T Certificates.P43Gen

@[expose] noncomputable def el0 (d : List Nat) : CV 45 := (genC PSp43.QP45 d).getD 1

@[expose] noncomputable def elA (d : List Nat) : CV 45 := (genC PSp43.QA45 d).getD 1

@[expose, reducible] noncomputable def reps0 : List (CV 45) :=
  [cOf (Certificates.P43Twin.tA ()), cOf (Certificates.P43Twin.tB ())]

@[expose, reducible] noncomputable def repsA : List (CV 45) :=
  [cOf (Certificates.P43Twin.tA ()), cOf (Certificates.P43Twin.tB ()),
    cOf (Certificates.P43Twin.t36 ()), cOf (Certificates.P43Twin.t540 ())]

@[expose, reducible] noncomputable def Q1 : List (CV 45) :=
  q8B (cOf (Certificates.P43Twin.tA ())) (cOf (Certificates.P43Twin.a1 ()))
    (cOf (Certificates.P43Twin.b1 ()))

@[expose, reducible] noncomputable def Q2 : List (CV 45) :=
  q8B (cOf (Certificates.P43Twin.tA ())) (cOf (Certificates.P43Twin.a2 ()))
    (cOf (Certificates.P43Twin.b2 ()))

@[expose] noncomputable def cents0 : List (List (CV 45)) := C0.map (List.map el0)

@[expose] noncomputable def centsA : List (List (CV 45)) := CA.map (List.map elA)

theorem one0_mem : (1 : CV 45) ∈ elemsC PSp43.QP45 := by decide +kernel

theorem oneA_mem : (1 : CV 45) ∈ elemsC PSp43.QA45 := by decide +kernel

theorem cov0 : pickRun (elemsC PSp43.QP45) invC conjC (genC PSp43.QP45) reps0 (elemsC PSp43.QP45)
    W0 = some reps0 := by
  decide +kernel

theorem covA : pickRun (elemsC PSp43.QA45) invC conjC (genC PSp43.QA45) repsA (elemsC PSp43.QA45)
    WA = some repsA := by
  decide +kernel

theorem cent0_ok : reps0.map (centC (elemsC PSp43.QP45)) = cents0 := by decide +kernel

theorem centA_ok : repsA.map (centC (elemsC PSp43.QA45)) = centsA := by decide +kernel

theorem loc0 : (reps0.zip cents0).all (fun p => noOddB 12 p.2 &&
    pairChkG (cOf (Certificates.P43Twin.tA ())) Q1 Q2 p.1 p.2) = true := by
  decide +kernel

theorem locA : (repsA.zip centsA).all (fun p => noOddB 12 p.2 &&
    pairChkG (cOf (Certificates.P43Twin.tA ())) Q1 Q2 p.1 p.2) = true := by
  decide +kernel

theorem sig : sigmaChkG Q1 Q2 (cOf (Certificates.P43Twin.a1 ())) (cOf (Certificates.P43Twin.a2 ()))
    (cOf (Certificates.P43Twin.x1 ())) (cOf (Certificates.P43Twin.x2 ())) (elemsC PSp43.QP45) =
    true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.P43T
