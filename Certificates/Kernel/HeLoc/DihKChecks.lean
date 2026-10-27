module

public import Certificates.Kernel.HeLoc.SevenDefs
public import CFSG.RankThree.PartOne.KS.HeSevenDihedralDefs
public import Certificates.Data.Kernel.HeDihK
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.HeDih CFSG.RankThree.PartOne

@[expose] noncomputable def c1K (k : Nat) : Nat := A (65 + k)

theorem dih10128 : dihWK 8330 14 c1K heSevenRhoWord heSevenSigmaWord = true := by quickRfl

end CertificateChecks.KernelHeLoc.Seven

end
