module

public import Certificates.Data.Kernel.PCentExt
public import Certificates.Kernel.HS799102.ClassData
public import Certificates.Kernel.HS799102.ChainData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

#kc_repo #kc_json_gz CertificateChecks.KernelHS799102
  "Certificates/Kernel/HS799102/data/glue.json.gz" 14004 2759080059374875951
  (N1 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (N2 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (N3 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (W1 : List (List Nat)) (W2 : List (List Nat)) (W3 : List (List Nat))

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def siftB (g : Nat) : Bool :=
  Nat.beq (Nat.shiftRight g (100 * 7)) 0 && allN 100 (fun t => Nat.blt (pg 7 (mask 7) g t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) CertificateChecks.KernelHS100.HC.LR
      CertificateChecks.KernelHS100.HC.TRI CertificateChecks.KernelHS100.HC.BP 5 0 g

@[expose] noncomputable def memK (g v : Nat) : Bool :=
  siftB g && Nat.beq (pcomp 100 7 (mask 7) g v) (pcomp 100 7 (mask 7) v g)

end CertificateChecks.KernelHS799102

end
