module

public import Certificates.Data.Kernel.Q16Q16K
public import Certificates.Kernel.Q16J3.Data
public import CFSG.Certificates.Kernel.Census.ToMain
import all Certificates.Data.Kernel.Q16Q16K
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CertificateChecks.KernelQ16J3

open CFSG.KC.Q16Q16K CFSG.KC.Census

set_option maxRecDepth 400000

@[expose] noncomputable def q16J3R : List Rec := q16J3C.pts.toList.map (mkRec 32 5)

theorem q16J3_size : Nat.beq q16J3G.size 8 = true ∧ Nat.beq q16J3O.size 32 = true := by
  constructor <;> quickRfl

theorem q16J3_nodup : q16J3O.toList.Nodup := by decide +kernel

theorem q16J3_canon : q16J3G.toList.all (canon1 32 5) = true ∧
    q16J3C.pts.toList.all (canon1 32 5) = true ∧ q16J3PS.all (fun p => Nat.blt p 32) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> quickRfl

theorem q16J3_enum : penumOK 32 5 q16J3G q16J3PS q16J3C = true := by quickRfl

theorem q16J3F0 : allL (chkX 32 5 q16J3R) ((q16J3R.drop 0).take 32) = true := by quickRfl
theorem q16J3F1 : allL (chkX 32 5 q16J3R) ((q16J3R.drop 32).take 32) = true := by quickRfl
theorem q16J3F2 : allL (chkX 32 5 q16J3R) ((q16J3R.drop 64).take 32) = true := by quickRfl
theorem q16J3F3 : allL (chkX 32 5 q16J3R) ((q16J3R.drop 96).take 32) = true := by quickRfl
theorem q16J3F4 : allL (chkX 32 5 q16J3R) ((q16J3R.drop 128).take 32) = true := by quickRfl
theorem q16J3F5 : allL (chkX 32 5 q16J3R) ((q16J3R.drop 160).take 32) = true := by quickRfl
theorem q16J3F6 : allL (chkX 32 5 q16J3R) ((q16J3R.drop 192).take 32) = true := by quickRfl
theorem q16J3F7 : allL (chkX 32 5 q16J3R) (q16J3R.drop 224) = true := by quickRfl

end CertificateChecks.KernelQ16J3
