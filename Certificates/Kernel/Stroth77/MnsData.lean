module

public import Certificates.Data.Kernel.Stroth77.MnsK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelMns778702
  "Certificates/Kernel/Stroth77/data/mns-778702.json.gz" 3421 4615295499199032810
  (MTC : Nat) (AT : Nat) (ITC : Nat) (AM : Nat) (REPM : Nat) (RW : Nat) (EF : Nat) (PF : Nat)
  (AF : Nat) (LF : Nat) (LP : Nat) (NPC : Nat) (NW : Nat)

public section

namespace CertificateChecks.KernelMns778702

@[expose] noncomputable def tabs : CFSG.KC.Stroth77MN.Tabs :=
  ⟨MTC, AT, ITC, AM, REPM, RW, EF, PF, AF, LF, LP, NPC, NW⟩

end CertificateChecks.KernelMns778702
