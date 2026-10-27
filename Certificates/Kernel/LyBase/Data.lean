module

public import Certificates.Data.Kernel.LyBase.Check
public import Certificates.Kernel.LyGlue.Hex
public import Certificates.Kernel.LyBenes.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelLyBase "Certificates/Kernel/LyBase/data/chain.json.gz" 3037 4339763140199388309
  (S1 : List (List Nat)) (S2 : List (List Nat)) (R0 : Nat) (R1 : Nat) (O2 : List Nat)
  (T2 : List (Nat × Nat))

namespace CertificateChecks.KernelLyBase

open CFSG.KC.LyBase CertificateChecks.KernelLy CertificateChecks.KernelLyB

@[expose] noncomputable def base : List Nat := [0, 3, 1]

@[expose] noncomputable def wB (r : List (Fin 6 × Bool)) : Bool := bFix cL dL base r

@[expose] noncomputable def W0 : List (List Nat) := [[NS 0], [NS 1], [NS 2], [NS 3], [NS 4], [NS 5]]

@[expose] noncomputable def W1 : List (List Nat) := S1.map fun w => w.map NS

end CertificateChecks.KernelLyBase

end
