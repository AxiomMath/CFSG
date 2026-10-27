module

public import Certificates.Kernel.StdOdd.RootOrbitChecks
public import Certificates.Kernel.StdOdd.RootOrbitBridge
public import Certificates.Kernel.Misc.E6StdSlp

public section

namespace CFSG.KD.StdOdd.Orbit

open CFSG.KC.StdOdd.Orbit CFSG.KS.StdOdd.Orbit CFSG.KC.Misc.E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.MatrixModel Matrix

theorem bits : OrbitBits RO.PL AM BM 3968055 RO.r :=
  rootOrbit_sound lenOK rOK rootOK' sortOK' validA validB fullA fullB RO.cA RO.cB start RO.s last

theorem facts :
    ∃ (pts : ℕ → Fin 78 → K) (dep : ℕ → ℕ),
      (∀ i < 3968055, ∀ j < 3968055, pts i = pts j → i = j) ∧
      (∃ r < 3968055, pts r = Pi.single 7 1) ∧
      (∀ i < 3968055, ∃ j < 3968055, pts j = toMat nativeAB.1 *ᵥ pts i) ∧
      (∀ i < 3968055, ∃ j < 3968055, pts j = toMat nativeAB.2 *ᵥ pts i) ∧
      (∀ i < 3968055, dep i = 0 → pts i = Pi.single 7 1) ∧
      (∀ i < 3968055, 0 < dep i → ∃ j < 3968055, dep j < dep i ∧
        (pts i = toMat nativeAB.1 *ᵥ pts j ∨ pts i = toMat nativeAB.2 *ᵥ pts j ∨
          pts j = toMat nativeAB.2 *ᵥ pts i)) :=
  facts_of_bits rep_A rep_B bits

end CFSG.KD.StdOdd.Orbit

end
