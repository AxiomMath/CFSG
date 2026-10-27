module

public import Certificates.Data.Kernel.LyDce.Defs
public import Certificates.Kernel.LyBase.Data
public import Certificates.Kernel.LyReplay.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelLyDce "Certificates/Kernel/LyDce/data/facts.json.gz" 770759 4055732628688960846
  (nt : List (Nat × Nat)) (rep : List (List Nat)) (vw : List (List Nat)) (aw : List (List Nat))
  (steps : List (List (Nat × Nat × List Nat × List Nat)))
  (dR : List (List Nat × List Nat)) (dLen : List (Nat × Nat))

namespace CertificateChecks.KernelLyDce

open CFSG.KC.LyDce CFSG.KC.LyReplay CertificateChecks.KernelLyBase

@[expose] noncomputable def factWith (nt' : Nat × Nat) (r v a : List Nat)
    (ss : List (Nat × Nat × List Nat × List Nat)) : Bool :=
  factOKD wB (rulesOf KernelLyReplay.kR) (rulesOf KernelLyReplay.eR) (rulesOf KernelLyReplay.tR)
    (rulesOf dR) nt' r v a ss

@[expose] noncomputable def factAt (i : Nat) : Bool :=
  factWith (nt.getD i (0, 0)) (rep.getD i []) (vw.getD i []) (aw.getD i []) (steps.getD i [])

end CertificateChecks.KernelLyDce

end
