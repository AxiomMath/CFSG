module

public import Certificates.Data.Kernel.HN14969.Bridge
import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#kc_repo #kc_json_gz_eval CertificateChecks.KernelHN14969
  "Certificates/Kernel/HN14969/data/hn14969.json.gz" 9679 7253863941293918395
  (iso : List (List Nat))
  (hS : Array (Array Nat)) (hBase : Array Nat) (hD : List (List Nat))
  (rS : Array (Array Nat)) (rBase : Array Nat) (rD : List (List Nat))
  (pS : Array (Array Nat)) (pBase : Array Nat) (pD : List (List Nat))

namespace CertificateChecks.KernelHN14969

open CFSG.KC.HN14969

@[expose] public def dH : List (List Int) := decW hD

@[expose] public def dR : List (List Int) := decW rD

@[expose] public def dP : List (List Int) := decW pD

end CertificateChecks.KernelHN14969
