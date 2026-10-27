module

public import Certificates.Data.Kernel.LyDce.Chain
public import Certificates.Kernel.LyBase.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelLyDce "Certificates/Kernel/LyDce/data/chains.json.gz" 508 1600968331486935281
  (sG : List (List (List Nat))) (b1 : List Nat) (m1 : List Nat) (r1 : List Nat)
  (t2 : List (List (List Nat))) (b2 : List Nat) (m2 : List Nat) (O2 : List (List Nat))
  (T2 : List (List (Nat × Nat)))

namespace CertificateChecks.KernelLyDce

open CFSG.KC.LyDce CertificateChecks.KernelLy CertificateChecks.KernelLyB

@[expose] def ordS : List Nat := [349920, 10080, 2880, 750]

@[expose] noncomputable def chainWith (n : Nat) (G : List (List Nat)) (t : List (List Nat))
    (a b : Nat) : Bool :=
  chainOK cL dL NS G (b1.getD n 0) a (r1.getD n 0) t (b2.getD n 0) b (O2.getD n [])
    (T2.getD n []) (ordS.getD n 0)

@[expose] noncomputable def chainAt (n : Nat) : Bool :=
  chainWith n (sG.getD n []) (t2.getD n []) (m1.getD n 0) (m2.getD n 0)

end CertificateChecks.KernelLyDce

end
