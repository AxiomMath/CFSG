module

public import Certificates.Data.Kernel.GMS78RuCzJ
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelGMS78.CzJ

#kc_repo #kc_json_gz CertificateChecks.KernelGMS78.CzJ
  "Certificates/Kernel/GMS78/data/CzJData.json.gz" 113780 1497403770932942742
  (LKs : List Nat) (PAR : Nat) (LAB : Nat) (INV : Nat) (KQ : Nat) (KW : Nat) (FIX : List Nat)
  (D3 : List Nat) (D5 : List Nat) (CT : List Nat) (SOLS : List Nat)

@[expose] noncomputable def LK (k : Nat) : Nat := CFSG.KC.GMS.neGet 0 LKs k

end CertificateChecks.KernelGMS78.CzJ
