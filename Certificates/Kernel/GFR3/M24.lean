module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3M24Inputs
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.GFR3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3M24Inputs
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGFR3.M24

open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def d : List (List ℤ) := m24ThreeWords.toList.drop 2

meta def ab : Array (Array Nat) := #[m24ThreeA, m24ThreeB]

end CertificateChecks.KernelGFR3.M24

end

#ks_rawchain CertificateChecks.KernelGFR3.M24.C 24 5 24
  CFSG.HardMathSupport.Solomon.Coordinator.m24ThreeArrs
  CFSG.HardMathSupport.Solomon.Coordinator.m24ThreeBaseArr 2 CertificateChecks.KernelGFR3.M24.d
#kmisc_packarrs CertificateChecks.KernelGFR3.M24.AB CertificateChecks.KernelGFR3.M24.ab 5
#kb3_enum CertificateChecks.KernelGFR3.M24.E
  CFSG.HardMathSupport.Solomon.Coordinator.m24ThreeGens
  CFSG.HardMathSupport.Solomon.Coordinator.m24ThreeBaseArr 24 5

public section

namespace CertificateChecks.KernelGFR3.M24

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.KC.GFR3K

theorem szOK' : szOK 24 5 = true := by quickRfl

theorem bA : arrBind m24ThreeA 24 5 (AB 0) = true := by quickRfl

theorem bB : arrBind m24ThreeB 24 5 (AB 1) = true := by quickRfl

theorem pAB : permB 24 5 (AB 0) = true ∧ permB 24 5 (AB 1) = true := ⟨by quickRfl, by quickRfl⟩

theorem bS : ∀ j < 12, arrBind m24ThreeArrs[j]! 24 5 (C.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bG : ∀ j < 3, arrBind m24ThreeGens[j]! 24 5 (E.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm : allN 12 (fun j => permOK 24 5 (mask 5) (24 * 5) (C.S j) (C.SI j)) = true := by
  quickRfl

theorem head : Nat.beq (C.S 0) (AB 0) = true ∧ Nat.beq (C.S 1) (AB 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bget : ∀ t < 9, m24ThreeBaseArr[t]! = pg 5 (mask 5) C.BP t := by decide +kernel

theorem siftG : ∀ k < 3, Nat.beq (Nat.shiftRight (E.G k) (24 * 5)) 0 = true ∧
    allN 24 (fun t => Nat.blt (pg 5 (mask 5) (E.G k) t) 24) = true ∧
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) C.LR C.TRI C.BP 9 0 (E.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels : relsK 24 5 3 C.BP (E.G 0) 9 m24ThreeRels = true := by quickRfl

theorem comm : commK 24 5 3 (E.G 0) E.G = true := by quickRfl

theorem x0 : permB 24 5 (E.G 0) = true ∧ Nat.beq (pw 24 5 (E.G 0) 3) (pidn 24 5) = true ∧
    (!Nat.beq (E.G 0) (pidn 24 5)) = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rc : Nat.beq (rcnt (C.LR 0)) 24 = true := by quickRfl

theorem tail : allN 24 (ptailBranchK 24 5 C.LR C.TR C.BP (E.G 0) (pw 24 5 (E.G 0))
    m24ThreeRels E.N E.T 9) = true := by quickRfl

theorem orb : ((List.range 9).map fun i => rcnt (C.LR i)) = [24, 23, 22, 21, 20, 16, 3, 1, 1] := by
  decide +kernel

theorem n0 : Nat.beq E.N 1080 = true ∧ Nat.beq E.ng 3 = true := ⟨by quickRfl, by quickRfl⟩

theorem cls : allN 1080 (gfr3AtK 24 5 1080 E.T 1080 3 1) = true := by quickRfl

theorem clsNeg : (!allN 1080 (gfr3AtK 24 5 1080 E.T 540 3 1)) = true := by quickRfl

end CertificateChecks.KernelGFR3.M24

end
