module

public import Certificates.Data.Kernel.SortTree
public import Certificates.Data.Kernel.MatConj22
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CertificateChecks.Conj3054 GL "Certificates/Kernel/MonsterB/Conj3054/data/gens.bin" 1408 4 33792 7606005276917512644

#kc_repo #kc_ktree CertificateChecks.Conj3054 REC "Certificates/Kernel/MonsterB/Conj3054/data/rec.bin" 4096 4 3643200 9579413092536764579

#kc_repo #kc_ktree CertificateChecks.Conj3054 EDGE "Certificates/Kernel/MonsterB/Conj3054/data/edge.bin" 3072 4 2732400 7615273123270672352

public section

namespace CertificateChecks.Conj3054

open CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.MatConj

@[expose] def rootK : Nat :=
  0x81e0050780121e0044780109e0041781e03e0780381e0160780681e01c078004000008001711f03c27c0505f00c0fc0300f00c05c0301b00c07400001

@[expose] noncomputable def actC (k n : Nat) : Nat :=
  (fun L => conjM (Nat.land L (maskN 484)) (Nat.shiftRight L 512) n) (GL k)

@[expose] noncomputable def recC : Nat → Nat := recT REC 6 512

@[expose] noncomputable def edgeC (i k : Nat) : Nat := fget (recT EDGE 6 384 i) k 16

end CertificateChecks.Conj3054

end
