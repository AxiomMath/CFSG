module

public import CFSG.Sporadic.HNOddCore.CCheckInputs

public section

namespace CertificateChecks.KernelSporSch.HNCTabNeg

open CFSG.Sporadic.HNOddCore.Native

theorem pos : (cRecStep #[1, 2, 0] #[0, 1, 2] #[0, 0, 2] #[1, 2, 0] #[0, 1, 2] #[0, 1, 2] 1 &&
    cRecStep #[1, 2, 0] #[0, 1, 2] #[0, 0, 2] #[1, 2, 0] #[0, 1, 2] #[0, 1, 2] 2) = true := by
  decide +kernel

theorem neg_entry :
    (!cRecStep #[1, 2, 0] #[0, 1, 2] #[0, 0, 2] #[1, 2, 0] #[0, 1, 2] #[0, 2, 1] 1) = true := by
  decide +kernel

theorem neg_entry2 :
    (!cRecStep #[1, 2, 0] #[0, 1, 2] #[0, 0, 2] #[1, 2, 0] #[0, 1, 2] #[0, 1, 0] 2) = true := by
  decide +kernel

theorem neg_par :
    (!cRecStep #[1, 2, 0] #[0, 1, 2] #[0, 4, 2] #[1, 2, 0] #[0, 1, 2] #[0, 1, 2] 1) = true := by
  decide +kernel

end CertificateChecks.KernelSporSch.HNCTabNeg
