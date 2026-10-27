module

public import Certificates.Data.Kernel.LyReplay.Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelLyReplay "Certificates/Kernel/LyReplay/data/replay.json.gz" 107289 12815633941351351443
  (starts : List (List Nat)) (steps : List (List (Nat × Nat × List Nat × List Nat)))
  (kR : List (List Nat × List Nat)) (eR : List (List Nat × List Nat))
  (tR : List (List Nat × List Nat))

namespace CertificateChecks.KernelLyReplay

open CFSG.KC.LyReplay

@[expose] noncomputable def replayAt (i : Nat) : Bool :=
  replayW (rulesOf kR) (rulesOf eR) (rulesOf tR) (wordOf (starts.getD i [])) (steps.getD i [])

end CertificateChecks.KernelLyReplay

end
