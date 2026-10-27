module

public import Certificates.Kernel.UnitarySix.Sec3.G3601
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Y14Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

@[expose] noncomputable def y14K (s : Fin 12) : Bool :=
  (List.range 9).all fun i =>
    Nat.beq (wK (cjW y14V[s.val]! [y14Basis[i]!])) (wK (iotaWordOf (colBits s i)))

theorem kY0 : ∀ s : Fin 12, s.val < 4 → y14K s = true := by decide +kernel
theorem kY1 : ∀ s : Fin 12, 4 ≤ s.val → s.val < 8 → y14K s = true := by decide +kernel
theorem kY2 : ∀ s : Fin 12, 8 ≤ s.val → y14K s = true := by decide +kernel

theorem y14_lt : ∀ s : Fin 12, ∀ i < 9, (∀ k ∈ cjW y14V[s.val]! [y14Basis[i]!], k < 18) ∧
    ∀ k ∈ iotaWordOf (colBits s i), k < 18 := by
  decide +kernel

theorem y14_k : y14Check = true := by
  unfold y14Check
  refine List.all_eq_true.2 fun s _ => List.all_eq_true.2 fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have hs : y14K s = true := by
    rcases Nat.lt_or_ge s.val 4 with h | h
    · exact kY0 s h
    rcases Nat.lt_or_ge s.val 8 with h' | h'
    · exact kY1 s h h'
    · exact kY2 s h'
  rw [eqA_wA (y14_lt s i hi').1 (y14_lt s i hi').2]
  exact List.all_eq_true.1 hs i hi

end CertificateChecks.KernelU6.Sec3
