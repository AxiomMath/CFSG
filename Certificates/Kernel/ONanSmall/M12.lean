module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import Certificates.Data.Kernel.ONanSmall.KTree
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import Certificates.Kernel.ONanSmall.Data.M12

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.M12

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.Sporadic.Schreier CFSG.KD.ONS.M12

@[expose] noncomputable def el (d : List Nat) : CV 24 := (genC m12D d).getD 1

@[expose] noncomputable def reps : List (CV 24) := R.map el

@[expose] noncomputable def cents : List (List (CV 24)) := C.map (List.map el)

theorem one_mem : (1 : CV 24) ∈ elemsC m12D := by decide +kernel

theorem pick : pickRun (elemsC m12D) invC conjC (genC m12D) [] (elemsC m12D) W = some reps := by
  decide +kernel

theorem cent_ok : reps.map (centC (elemsC m12D)) = cents := by decide +kernel

@[expose] noncomputable def kt : KTree (CV 24) := KTree.ofList Subtype.val (K0.map el)

theorem t0_mem : memB (K0.map el) (reps.getD 0 1) = true := by decide +kernel

theorem cls0 : (TsC m12D).all (fun T => T.all fun u => (K0.map el).all fun k =>
    KTree.memK Subtype.val (u⁻¹ * k * u) kt) = true := by
  decide +kernel

theorem k9747 : (reps.zip cents).all (fun p => noOddB3 100 p.2 &&
    if p.1 = reps.getD 0 1 then pairsVKF 100 [1] (K0.map el) true p.1 p.2
    else pairsV 100 [1] (elemsC m12D) true p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.M12
