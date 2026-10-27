module

public import CFSG.Certificates.Kernel.M3BFib.Fib0Sound
public import Certificates.Kernel.M3BFib.Lit
public import Certificates.Kernel.M3BFib.Fib0
public import Certificates.Kernel.M3BFib.Fib0For
public import Certificates.Kernel.M3BFib.Roots0

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.Monster.Generated
open Timmesfeld.M3B (fT fLam fpt unpack nPts fRootV repD)


theorem m3bf_roots0 (hinv : letterInvCheck () = true) :
    ∀ p < nPts, ∀ x : Gmat, IsAct tbSys x (toD (fpt (fT 0) (fLam 0) (unpack p))) →
      ∃ g ∈ tbL, ∃ v ∈ fRootV 0, IsAct tbSys (g⁻¹ * x * g) (toD (repD 0 v)) :=
  fibre0_roots_of_checks (os := [o0_0, o0_1, o0_2, o0_3, o0_4, o0_5, o0_6, o0_7]) (n := 8) hinv
    m3bf_lk m3bf_word0 m3bf_gen0 m3bf_lam0 m3bf_coord0 m3bf_norm0 m3bf_hn0 m3bf_tab0 m3bf_root0
    m3bf_rootv0 m3bf_mask0 fun j hj => by
      interval_cases j
      · exact m3bf_for0_0
      · exact m3bf_for0_1
      · exact m3bf_for0_2
      · exact m3bf_for0_3
      · exact m3bf_for0_4
      · exact m3bf_for0_5
      · exact m3bf_for0_6
      · exact m3bf_for0_7

end CFSG.KC.M3BF

end
