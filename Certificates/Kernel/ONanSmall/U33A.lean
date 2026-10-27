module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import Certificates.Data.TL4MF163U3Inv
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMCheck
public import Certificates.Kernel.ONanSmall.Data.U33A

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.U33A

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.GH74.KGroups CFSG.KD.ONS.U33A

@[expose] noncomputable def el (d : List Nat) : CV 28 := (genC U33.QA d).getD 1

@[expose] noncomputable def reps : List (CV 28) := R.map el

@[expose] noncomputable def cents : List (List (CV 28)) := C.map (List.map el)

theorem one_mem : (1 : CV 28) ∈ elemsC U33.QA := by decide +kernel

theorem pick : pickRun (elemsC U33.QA) invC conjC (genC U33.QA) [] (elemsC U33.QA) W =
    some reps := by
  decide +kernel

theorem cent_ok : reps.map (centC (elemsC U33.QA)) = cents := by decide +kernel

theorem cls1 : (elemsC U33.QA).all (fun g => memB (K1.map el) (g⁻¹ * reps.getD 1 1 * g)) = true := by
  decide +kernel

theorem k9744 : (reps.zip cents).all (fun p => noOddB3 100 p.2 &&
    if p.1 = reps.getD 1 1 then pairsVK 100 (elemsC U33.QP) (K1.map el) false p.1 p.2
    else pairsV 100 (elemsC U33.QP) (elemsC U33.QA) false p.1 p.2) = true := by
  decide +kernel

theorem k55111 : (reps.zip cents).all (fun p =>
    Certificates.TL4MF163U3Inv.centInvAt (elemsC U33.QP) p.1 p.2) = true := by
  decide +kernel

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM in
theorem k397508 : (reps.zip cents).all (fun p => nqAt (fun _ => true) p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.U33A
