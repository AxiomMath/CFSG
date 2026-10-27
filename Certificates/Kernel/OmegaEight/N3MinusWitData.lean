module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelO8

#kc_repo #kc_json_gz CertificateChecks.KernelO8
  "Certificates/Kernel/OmegaEight/data/N3MinusWitData.json.gz" 435646 3211042272012570487
  (N3mIX : Nat) (N3mLinL : List (List (List Nat) × List Nat × List Nat))
  (N3mNC : List (List Nat) × List Nat × List Nat) (N3mMaxY : List Nat)

@[expose] noncomputable def N3mLin (a b : Nat) : List (List Nat) × List Nat × List Nat :=
  N3mLinL.getD (48 * a + b) ([], [], [])

end CertificateChecks.KernelO8
