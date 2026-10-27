module

public import Certificates.Data.Kernel.HSPinned6101
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelHSPinned6101

#kc_repo #kc_json_gz CertificateChecks.KernelHSPinned6101
  "Certificates/Kernel/HSPinned6101/data/HSPinned6101.json.gz" 326561 16095602065327621211
  (nA : Nat) (PA : Nat) (TAA : Nat) (TBA : Nat) (PRA : Nat) (LBA : Nat) (PSA : Nat)
  (nN : Nat) (PN : Nat) (TAN : Nat) (TBN : Nat) (PRN : Nat) (LBN : Nat) (PSN : Nat)
  (LM : Nat) (VAB : Nat)

open Certificates.Kernel.HSPinned6101 in
@[expose] noncomputable def dA : PD := ⟨nA, PA, TAA, TBA, PRA, LBA, PSA⟩

open Certificates.Kernel.HSPinned6101 in
@[expose] noncomputable def dN : PD := ⟨nN, PN, TAN, TBN, PRN, LBN, PSN⟩

end CertificateChecks.KernelHSPinned6101

end
