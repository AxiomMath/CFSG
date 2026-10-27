module

public import Certificates.Data.Kernel.SmithD6.Data
public import Certificates.Data.Kernel.KeyTreeChunks
public import Certificates.Data.SmithD6Model
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Lines

open CFSG.SmithD6

@[expose] def lkOK (k : Nat) : Bool :=
  Nat.blt 0 (k / 4096) && Nat.blt (k / 4096) (k % 4096) &&
    Nat.blt (k % 4096) ((k / 4096) ^^^ (k % 4096)) &&
    Nat.blt ((k / 4096) ^^^ (k % 4096)) 4096 && !qf (k / 4096) && !qf (k % 4096) &&
    !bf (k / 4096) (k % 4096)

@[expose] noncomputable def lkAll (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun k _ ih => lkOK k && ih) l

end CertificateChecks.SmithD6Lines

end

open CFSG.KD.SmithD6 CertificateChecks.SmithD6Lines

#kc_each CertificateChecks.SmithD6Lines d6lk (fun c => lkAll (CFSG.KC.KeyTree.nthC J.lineKeysC c))
  0 179

public section

namespace CertificateChecks.SmithD6Lines

#kc_forall_chunks lineKeys_ok (fun c => lkAll (CFSG.KC.KeyTree.nthC J.lineKeysC c) = true)
  179 CertificateChecks.SmithD6Lines.d6lk 1

end CertificateChecks.SmithD6Lines

end
