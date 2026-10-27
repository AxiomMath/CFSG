module

public import Certificates.Kernel.HeLoc.SevenDefs
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

@[expose] noncomputable def mem1 (i : Nat) : Bool := memI (Nat.add 250 i)

end CertificateChecks.KernelHeLoc.Seven

#kss_each CertificateChecks.KernelHeLoc.Seven.M1 CertificateChecks.KernelHeLoc.Seven.mem1 250

end
