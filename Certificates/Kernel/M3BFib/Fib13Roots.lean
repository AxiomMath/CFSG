module

public import CFSG.Certificates.Kernel.M3BFib.Fib13Sound
public import Certificates.Kernel.M3BFib.Lit
public import Certificates.Kernel.M3BFib.Fib1
public import Certificates.Kernel.M3BFib.Fib2
public import Certificates.Kernel.M3BFib.Fib3
public import Certificates.Kernel.M3BFib.Roots13

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.Monster.Generated
open Timmesfeld.M3B (fT fLam fpt unpack nPts fRootV repD)


theorem m3bf_roots1 (hinv : letterInvCheck () = true) :
    ∀ p < nPts, ∀ x : Gmat, IsAct tbSys x (toD (fpt (fT 1) (fLam 1) (unpack p))) →
      ∃ g ∈ tbL, ∃ v ∈ fRootV 1, IsAct tbSys (g⁻¹ * x * g) (toD (repD 1 v)) :=
  fibre_roots_of_checks hinv (by decide) m3bf_lk rfl m3bf_t1 m3bf_word1 m3bf_gen1 m3bf_lam1
    m3bf_bas1 m3bf_for1 m3bf_root1

theorem m3bf_roots2 (hinv : letterInvCheck () = true) :
    ∀ p < nPts, ∀ x : Gmat, IsAct tbSys x (toD (fpt (fT 2) (fLam 2) (unpack p))) →
      ∃ g ∈ tbL, ∃ v ∈ fRootV 2, IsAct tbSys (g⁻¹ * x * g) (toD (repD 2 v)) :=
  fibre_roots_of_checks hinv (by decide) m3bf_lk rfl m3bf_t2 m3bf_word2 m3bf_gen2 m3bf_lam2
    m3bf_bas2 m3bf_for2 m3bf_root2

theorem m3bf_roots3 (hinv : letterInvCheck () = true) :
    ∀ p < nPts, ∀ x : Gmat, IsAct tbSys x (toD (fpt (fT 3) (fLam 3) (unpack p))) →
      ∃ g ∈ tbL, ∃ v ∈ fRootV 3, IsAct tbSys (g⁻¹ * x * g) (toD (repD 3 v)) :=
  fibre_roots_of_checks hinv (by decide) m3bf_lk rfl m3bf_t3 m3bf_word3 m3bf_gen3 m3bf_lam3
    m3bf_bas3 m3bf_for3 m3bf_root3

end CFSG.KC.M3BF

end
