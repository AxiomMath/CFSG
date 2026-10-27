module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import Certificates.Data.TL4LieZ2Inv
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMCheck
public import Certificates.Kernel.ONanSmall.Data.L33

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.L33

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.GH74.KGroups CFSG.KD.ONS.L33

@[expose] noncomputable def elP (d : List Nat) : CV 26 := (genC L33.QP d).getD 1

@[expose] noncomputable def elA (d : List Nat) : CV 26 := (genC L33.QA d).getD 1

@[expose] noncomputable def repsP : List (CV 26) := RP.map elP

@[expose] noncomputable def repsA : List (CV 26) := RA.map elA

@[expose] noncomputable def centsP : List (List (CV 26)) := CP.map (List.map elP)

@[expose] noncomputable def centsPA : List (List (CV 26)) := CPA.map (List.map elA)

@[expose] noncomputable def centsA : List (List (CV 26)) := CA.map (List.map elA)

theorem oneP_mem : (1 : CV 26) ∈ elemsC L33.QP := by decide +kernel

theorem oneA_mem : (1 : CV 26) ∈ elemsC L33.QA := by decide +kernel

theorem pickP : pickRun (elemsC L33.QP) invC conjC (genC L33.QP) [] (elemsC L33.QP) WP =
    some repsP := by
  decide +kernel

theorem pickA : pickRun (elemsC L33.QA) invC conjC (genC L33.QA) [] (elemsC L33.QA) WA =
    some repsA := by
  decide +kernel

theorem centP_ok : repsP.map (centC (elemsC L33.QP)) = centsP := by decide +kernel

theorem centPA_ok : repsP.map (centC (elemsC L33.QA)) = centsPA := by decide +kernel

theorem centA_ok : repsA.map (centC (elemsC L33.QA)) = centsA := by decide +kernel

theorem k55123 : ((repsP.zip centsP).zip centsPA).all (fun p =>
    Certificates.TL4LieZ2Inv.q8InvAt p.1.1 p.1.2 p.2) = true := by
  decide +kernel

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM in
theorem k397508 : (repsA.zip centsA).all (fun p => nqAt (fun _ => true) p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.L33
