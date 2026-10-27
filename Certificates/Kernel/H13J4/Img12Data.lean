module

public import CFSG.Certificates.Kernel.J4.DceS
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelH13.Img12 "Certificates/Kernel/H13J4/data/img12.json.gz"
  34187 15336904802366441862
  (UP : Nat) (VP : Nat) (EL : List Nat) (ne : Nat) (LV : List Nat)

namespace CertificateChecks.KernelH13.Img12

@[expose] noncomputable def LET : Nat := Nat.lor UP (Nat.shiftLeft VP 288)

@[expose] noncomputable def ET (e : Nat) : Nat := EL.getD e 0

@[expose] def GM : Nat := 5

end CertificateChecks.KernelH13.Img12

end
