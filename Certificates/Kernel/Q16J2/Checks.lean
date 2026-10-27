module

public import Certificates.Data.Kernel.Q16Q16K
public import Certificates.Kernel.Q16J2.Data
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
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

namespace CertificateChecks.KernelQ16J2

open CFSG.KC.Q16Q16K CFSG.KC.Census

set_option maxRecDepth 400000

@[expose] noncomputable def q16J2R : List Rec := q16J2C.pts.toList.map (mkRec 16 4)

theorem q16J2_size : Nat.beq q16J2G.size 3 = true ∧ Nat.beq q16J2O.size 16 = true := by
  constructor <;> quickRfl

theorem q16J2_bind : ((List.range 3).all fun k => (List.range 16).all fun q =>
    Nat.blt q16J2O[q]! 315 &&
      Nat.beq (CFSG.ComponentClassification.J2Cover.sylowStrong[k]!)[q16J2O[q]!]!
        q16J2O[at' 4 q16J2G[k]! q]!) = true := by
  quickRfl

theorem q16J2_nodup : q16J2O.toList.Nodup := by decide +kernel

theorem q16J2_canon : q16J2G.toList.all (canon1 16 4) = true ∧
    q16J2C.pts.toList.all (canon1 16 4) = true ∧ q16J2PS.all (fun p => Nat.blt p 16) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> quickRfl

theorem q16J2_enum : penumOK 16 4 q16J2G q16J2PS q16J2C = true := by quickRfl

theorem q16J2F0 : allL (chkX 16 4 q16J2R) ((q16J2R.drop 0).take 32) = true := by quickRfl
theorem q16J2F1 : allL (chkX 16 4 q16J2R) ((q16J2R.drop 32).take 32) = true := by quickRfl
theorem q16J2F2 : allL (chkX 16 4 q16J2R) ((q16J2R.drop 64).take 32) = true := by quickRfl
theorem q16J2F3 : allL (chkX 16 4 q16J2R) ((q16J2R.drop 96).take 32) = true := by quickRfl
theorem q16J2F4 : allL (chkX 16 4 q16J2R) ((q16J2R.drop 128).take 32) = true := by quickRfl
theorem q16J2F5 : allL (chkX 16 4 q16J2R) ((q16J2R.drop 160).take 32) = true := by quickRfl
theorem q16J2F6 : allL (chkX 16 4 q16J2R) ((q16J2R.drop 192).take 32) = true := by quickRfl
theorem q16J2F7 : allL (chkX 16 4 q16J2R) (q16J2R.drop 224) = true := by quickRfl

end CertificateChecks.KernelQ16J2
