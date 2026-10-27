module

public import CFSG.Certificates.Kernel.E7PlaneGlue
public import Certificates.Kernel.E7Plane.Bridge
public import Certificates.Kernel.E7Plane.Checks

public section

namespace CFSG.KD.E7Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore CFSG.KC.E7Plane


theorem sylGood_two : SylGood 2 1024 :=
  sylK_sound RV_eq_e7Certificate_roots TB_eq_e7Certificate_table (by norm_num) sylK_two

theorem sylGood_three : SylGood 3 81 :=
  sylK_sound RV_eq_e7Certificate_roots TB_eq_e7Certificate_table (by norm_num) sylK_three

theorem sylGood_five : SylGood 5 5 :=
  sylK_sound RV_eq_e7Certificate_roots TB_eq_e7Certificate_table (by norm_num) sylK_five

theorem sylGood_seven : SylGood 7 7 :=
  sylK_sound RV_eq_e7Certificate_roots TB_eq_e7Certificate_table (by norm_num) sylK_seven

theorem e7Plane_pair_kernel (φ ψ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Z3)
    (w : WeylGroup .E7) (hφ : w ∈ charStabilizer φ) (hψ : w ∈ charStabilizer ψ) :
    w ∈ kernelWeylGroup (φ.prod ψ) ∨ CyclicTriple .E7 (kernelRoots (φ.prod ψ)) w :=
  e7Plane_of_sylGood sylGood_two sylGood_three sylGood_five sylGood_seven φ ψ w hφ hψ

end CFSG.KD.E7Plane

end
