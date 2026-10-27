module

public import CFSG.Sporadic.Recognition.HSMultiplierInputs

public section

namespace CertificateChecks.KernelHSMult

open CFSG.CosetTable CFSG.Sporadic.Recognition.HSMultiplier

@[expose] def hsPairs : List (List (Fin 6 × Bool) × List (Fin 2 × Bool)) :=
  hsRels.map (fun r => (r, [])) ++ (List.finRange 6).map (fun i => ((i, false) :: hsCommWord i, [])) ++
    [(hsSurjA, [(0, false)]), (hsSurjB, [(1, false)])]

theorem hsCheckWords_eq :
    hsCheckWords = hsPairs.map fun q => substWord hsGenWords q.1 ++ q.2 := by
  simp [hsCheckWords, hsPairs, Function.comp_def]

end CertificateChecks.KernelHSMult

end
