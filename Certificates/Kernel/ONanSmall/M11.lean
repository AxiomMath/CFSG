module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import Certificates.Data.TL4LieZ2Inv
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMCheck
public import Certificates.Kernel.ONanSmall.Data.M11

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.M11

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.GH74.KGroups CFSG.KD.ONS.M11

@[expose] noncomputable def el (d : List Nat) : CV 11 := (genC M11.Q d).getD 1

@[expose] noncomputable def reps : List (CV 11) := R.map el

@[expose] noncomputable def cents : List (List (CV 11)) := C.map (List.map el)

theorem one_mem : (1 : CV 11) ∈ elemsC M11.Q := by decide +kernel

theorem pick : pickRun (elemsC M11.Q) invC conjC (genC M11.Q) [] (elemsC M11.Q) W = some reps := by
  decide +kernel

theorem cent_ok : reps.map (centC (elemsC M11.Q)) = cents := by decide +kernel

theorem k55123 : (reps.zip cents).all (fun p =>
    Certificates.TL4LieZ2Inv.q8InvAt p.1 p.2 p.2) = true := by
  decide +kernel

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM in
theorem k397508 : (reps.zip cents).all (fun p => nqAt (fun _ => true) p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.M11
