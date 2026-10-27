module

public import Certificates.Data.Kernel.EvenSporSuz.Defs
public import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSyl25002.ST CFSG.EvenSporadicStandard.TwoSuz.treeText

#kc_repo #kc_json_gz CertificateChecks.KernelSyl25002
  "Certificates/Kernel/EvenSporSuz/data/tree25002.json.gz" 320788 3746019641113067603
  (tp : List (Nat × Nat)) (ps : List Nat) (iv : List Nat)

namespace CertificateChecks.KernelSyl25002

@[expose] noncomputable def tokT : List (List Char) :=
  ((CFSG.KC.EvenSporSuz.linesK ST.chars).getD 1 []).splitOn ' '

end CertificateChecks.KernelSyl25002
