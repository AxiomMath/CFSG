module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import Certificates.Data.GH74.PSp43NoQ8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import Certificates.Kernel.ONanSmall.Data.P43A

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.P43A

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.ComponentClassification.CatFactsSmall CFSG.KD.ONS.P43A

@[expose] noncomputable def el (d : List Nat) : CV 45 := (genC PSp43.QA45 d).getD 1

@[expose] noncomputable def reps : List (CV 45) := R.map el

@[expose] noncomputable def cents : List (List (CV 45)) := C.map (List.map el)

theorem one_mem : (1 : CV 45) ∈ elemsC PSp43.QA45 := by decide +kernel

theorem pick : pickRun (elemsC PSp43.QA45) invC conjC (genC PSp43.QA45) [] (elemsC PSp43.QA45) W =
    some reps := by
  decide +kernel

theorem cent_ok : reps.map (centC (elemsC PSp43.QA45)) = cents := by decide +kernel

theorem k9746 : (reps.zip cents).all (fun p => noOddB3 100 p.2 &&
    pairsV 100 (elemsC PSp43.QP45) (elemsC PSp43.QA45) false p.1 p.2) = true := by
  decide +kernel

theorem k55108 : (reps.zip cents).all (fun p =>
    Certificates.PSp43NoQ8.noQ8PairsB p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.P43A
