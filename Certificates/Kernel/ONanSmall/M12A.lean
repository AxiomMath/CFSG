module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import Certificates.Kernel.ONanSmall.Data.M12A

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.M12A

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.Sporadic.Schreier CFSG.KD.ONS.M12A

@[expose, reducible] noncomputable def sig : CV 24 := cOf m12Sigma

@[expose, reducible] noncomputable def LA : List (CV 24) :=
  elemsC m12D ++ (elemsC m12D).map (sig * ·)

@[expose] noncomputable def el (d : List Nat) : CV 24 := (genA m12D sig d).getD 1

@[expose] noncomputable def reps : List (CV 24) := R.map el

@[expose] noncomputable def cents : List (List (CV 24)) := C.map (List.map el)

theorem one_mem : (1 : CV 24) ∈ LA := by decide +kernel

theorem pick : pickRun LA invC conjC (genA m12D sig) [] LA W = some reps := by
  decide +kernel

theorem cent_ok : reps.map (centC LA) = cents := by decide +kernel

theorem k9748 : (reps.zip cents).all (fun p => noOddB3 100 p.2 &&
    pairsV 100 (elemsC m12D) LA false p.1 p.2) = true := by
  decide +kernel

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM in
theorem k397508 : (reps.zip cents).all (fun p =>
    nqAt (fun x => firstBlock (ev x)) p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.M12A
