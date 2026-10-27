
module

public import Certificates.Kernel.KDense.Y443.Fix
public import Certificates.Kernel.KDense.Y443.Tri
public import Certificates.Kernel.KDense.Y443.Bray

public section

namespace CertificateChecks.KernelKDense.Y443

open CFSG.Monster.AxisCount CFSG.YGroups.Y443

theorem c10107 : wordLin (wcWord ++ omegaWord) = wordLin (omegaWord ++ tWord) :=
  cAlign
theorem c10108 : wordLin (wcWord ++ omegaWord) = wordLin (omegaWord ++ tWord) :=
  cAlign
theorem c10110 : wordLin (wcWord ++ omegaWord) = wordLin (omegaWord ++ tWord) :=
  cAlign

theorem c10112 :
    wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP ++ omegaWord) = wordLin (omegaWord ++ coverPHat) ∧
      wordLin (powL 3 coverPHat) = 1 ∧ wordLin (coverQ ++ omegaWord) = wordLin (omegaWord ++ coverQHat) ∧
      wordLin (coverQHat ++ coverPHat ++ coverWy) = wordLin (coverWy ++ tWord) := cCover
theorem c10113 :
    wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP ++ omegaWord) = wordLin (omegaWord ++ coverPHat) ∧
      wordLin (powL 3 coverPHat) = 1 ∧ wordLin (coverQ ++ omegaWord) = wordLin (omegaWord ++ coverQHat) ∧
      wordLin (coverQHat ++ coverPHat ++ coverWy) = wordLin (coverWy ++ tWord) := cCover
theorem c10114 :
    wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP ++ omegaWord) = wordLin (omegaWord ++ coverPHat) ∧
      wordLin (powL 3 coverPHat) = 1 ∧ wordLin (coverQ ++ omegaWord) = wordLin (omegaWord ++ coverQHat) ∧
      wordLin (coverQHat ++ coverPHat ++ coverWy) = wordLin (coverWy ++ tWord) := cCover

theorem c10120 :
    wordLin (rhoWord ++ rhoWord) = 1 ∧
      (∀ s ∈ rhoGens, wordLin (Lw s ++ rhoWord) = wordLin (rhoWord ++ Lw (armSwapL s))) ∧
      wordLin (omegaWord ++ mWord) = wordLin (rhoWord ++ omegaWord) ∧
      wordLin (zmWord ++ qWord) = wordLin (qWord ++ tWord) := cP2
theorem c10121 :
    wordLin (rhoWord ++ rhoWord) = 1 ∧
      (∀ s ∈ rhoGens, wordLin (Lw s ++ rhoWord) = wordLin (rhoWord ++ Lw (armSwapL s))) ∧
      wordLin (omegaWord ++ mWord) = wordLin (rhoWord ++ omegaWord) ∧
      wordLin (zmWord ++ qWord) = wordLin (qWord ++ tWord) := cP2
theorem c10122 :
    wordLin (rhoWord ++ rhoWord) = 1 ∧
      (∀ s ∈ rhoGens, wordLin (Lw s ++ rhoWord) = wordLin (rhoWord ++ Lw (armSwapL s))) ∧
      wordLin (omegaWord ++ mWord) = wordLin (rhoWord ++ omegaWord) ∧
      wordLin (zmWord ++ qWord) = wordLin (qWord ++ tWord) := cP2

theorem c10124 :
    wordLin (tWord ++ swap13Word) = wordLin (swap13Word ++ tWord) ∧
      wordLin (mtmWord ++ swap13Word) = wordLin (swap13Word ++ zmWord) := cSwap
theorem c10125 :
    wordLin (tWord ++ swap13Word) = wordLin (swap13Word ++ tWord) ∧
      wordLin (mtmWord ++ swap13Word) = wordLin (swap13Word ++ zmWord) := cSwap
theorem c10126 :
    wordLin (tWord ++ swap13Word) = wordLin (swap13Word ++ tWord) ∧
      wordLin (mtmWord ++ swap13Word) = wordLin (swap13Word ++ zmWord) := cSwap

end CertificateChecks.KernelKDense.Y443

end
