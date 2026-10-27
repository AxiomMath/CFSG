module

public import Certificates.Kernel.Misc.Tits.Prim8077
public import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelT8074 "Certificates/Kernel/Tits8074/data/c8074.json.gz"
  26865 13530145791583852487
  (x0 : List (List Nat × Nat)) (x1 : List (List Nat × Nat)) (x2 : List (List Nat × Nat))
  (x3 : List (List Nat × Nat)) (x4 : List (List Nat × Nat)) (x5 : List (List Nat × Nat))
  (x6 : List (List Nat × Nat)) (x7 : List (List Nat × Nat)) (x8 : List (List Nat × Nat))
  (x9 : List (List Nat × Nat)) (x10 : List (List Nat × Nat)) (x11 : List (List Nat × Nat))
  (x12 : List (List Nat × Nat)) (x13 : List (List Nat × Nat)) (x14 : List (List Nat × Nat))
  (x15 : List (List Nat × Nat)) (zc : Nat) (aw : List Nat) (sc : Nat)
  (r2 : List (List Nat)) (r3 : List (List Nat)) (r4 : List (List Nat)) (r5 : List (List Nat))
  (r6 : List (List Nat)) (hw : List (List Nat)) (tg : List (List Nat)) (cw : List (List Nat))

namespace CertificateChecks.KernelT8074

open CertificateChecks.KernelMisc

@[expose] noncomputable def L (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (TitsPCh.S (Nat.shiftRight c 1))
    (fun _ _ => TitsPCh.SI (Nat.shiftRight c 1)) (Nat.land c 1)

end CertificateChecks.KernelT8074

end
