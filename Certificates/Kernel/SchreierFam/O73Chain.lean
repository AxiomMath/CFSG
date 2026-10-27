module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73Chain
public import Certificates.Data.Kernel.Misc.O73Chain
public import Certificates.Kernel.Sporadic.RawTreeGen
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73Chain
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public meta import Mathlib

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelSchreierFam

open CFSG.AGLEmbedding.R3.O73Three

meta def baseO73 : Array Nat := (chainBase.map Fin.val).toArray

@[expose] def dO73 : List (List ℤ) := chainW.toList.drop 2

@[expose] def msO73 : List (Matrix CFSG.LieType.Multipliers.O73.Idx CFSG.LieType.Multipliers.O73.Idx
    (ZMod 3)) :=
  [matA, matB, toMI rowsS2, toMI rowsS3, toMI rowsS4, toMI rowsS5, toMI rowsS6, toMI rowsS7,
    toMI rowsS8, toMI rowsS9, toMI rowsS10, toMI rowsS11, toMI rowsS12]

@[expose] def ordO73 : List ℕ := [3, 3, 12, 4, 2, 2, 3, 2, 3, 3, 3, 3, 3]

@[expose] noncomputable def ksO73 : List ℕ := msO73.map CFSG.KC.Misc.O73.matM7

end CertificateChecks.KernelSchreierFam

end

#ks_rawtree CertificateChecks.KernelSchreierFam.O73 2187 12 64 64 0
  CFSG.AGLEmbedding.R3.O73Three.chainS CertificateChecks.KernelSchreierFam.baseO73 2
  CertificateChecks.KernelSchreierFam.dO73

public section

namespace CertificateChecks.KernelSchreierFam.O73

open CFSG.AGLEmbedding.R3.O73Three CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.O73
  CertificateChecks.KernelSchreierFam

theorem tab : ∀ j < 13, tabM7 12 (S j) (ksO73.getD j 0) = true := by
  intro j hj
  interval_cases j <;> decide +kernel

theorem iso : ∀ j < 13, isoM7 (ksO73.getD j 0) = true := by
  intro j hj
  interval_cases j <;> decide +kernel

theorem cube : ∀ j < 2, Nat.beq (mulM7 (ksO73.getD j 0) (mulM7 (ksO73.getD j 0) (ksO73.getD j 0)))
    oneM7 = true := by
  intro j hj
  interval_cases j <;> decide +kernel

theorem words : ∀ j < 13, 2 ≤ j → wordOK ksO73 ordO73 (chainW.getD j []) j = true := by
  intro j hj h2
  interval_cases j <;> decide +kernel

theorem bget : ∀ t < 6, (chainBase.map Fin.val).toArray[t]! = pg 12 (mask 12) BP t := by
  decide +kernel

theorem orbProd : ((List.range 6).map fun i => rcnt (LR i)).prod = 4585351680 := by
  decide +kernel

end CertificateChecks.KernelSchreierFam.O73
