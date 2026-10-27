module

public import Certificates.Data.Kernel.Mat3
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverInputs

public section

namespace CertificateChecks.KernelONCover

open CFSG.KC.Mat3 CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover

@[expose] def hatG : List (List Nat) :=
  [[0, 1, 0, 6, 6, 0, 0, 0, 1], [3, 3, 0, 3, 1, 0, 0, 0, 1], [3, 2, 1, 0, 6, 0, 6, 3, 4], one3]

@[expose] def hatGi : List (List Nat) :=
  [[6, 6, 0, 1, 0, 0, 0, 0, 1], [1, 4, 0, 4, 3, 0, 0, 0, 1], [3, 2, 1, 0, 6, 0, 6, 3, 4], one3]

@[expose] def hatB : List Nat := [1, 0, 0]

@[expose] def hatSU : List (List (Fin 4 × Bool)) := cov.filter lowLetters ++ [[(3, false)]]

@[expose] def hatWordsU : List (List (Fin 4 × Bool) × ℕ) :=
  (zetaWord, 3) :: (substWord alphaImgs zetaWord ++ zetaWord, 1) ::
    hatSU.map fun ρ => (substWord alphaImgs ρ, 1)

theorem hat_ok : check 7 4 hatG hatGi hatB hatSU hatWordsU = true := by decide +kernel

end CertificateChecks.KernelONCover

end
