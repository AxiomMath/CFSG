module

import CFSG.Certificates.Kernel.Bounds.M24Alt.Binding
import CFSG.Monster.Schur.M24.Words

namespace CertificateChecks.Batch9267.Neg

open CFSG.Monster.Schur.M24

example : (a2 ++ a2).map (fun x => ((x.1 : ℕ), x.2)) ∉ CFSG.KBAlt.M24.rels := by decide +kernel

example : (r5.dropLast ++ [(1, false)]).map (fun x : Fin 2 × Bool => ((x.1 : ℕ), x.2)) ∉
    CFSG.KBAlt.M24.rels := by
  decide +kernel

end CertificateChecks.Batch9267.Neg
