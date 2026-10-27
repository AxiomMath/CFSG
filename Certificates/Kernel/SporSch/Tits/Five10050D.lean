module

public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.SporSch.Tits.GenMask
public import Certificates.Kernel.SporSch.Tits.GenAll5
public import Certificates.Data.Kernel.SporSch.TitsCnt
public import CFSG.RankThree.PartOne.KE.TitsFiveCheckInputs
meta import CFSG.RankThree.PartOne.KE.TitsFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.TitsInvCheck
meta import CFSG.Sporadic.Schreier.TitsInvCheck

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSporSch.TitsF 11 CFSG.RankThree.PartOne.KE.titsFiveArr
#kst_mask CertificateChecks.KernelSporSch.TitsMF CFSG.Sporadic.Schreier.Tits.titsHLevels
  CFSG.RankThree.PartOne.KE.titsFiveArr

namespace CertificateChecks.KernelSporSch.TitsFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] noncomputable def PFH (t0 t1 t2 t3 t4 : Nat) : Bool :=
  baseComm TitsH.BP 5 (gptR t0 t1 t2 t3 t4) (pgR TitsF)

@[expose] noncomputable def QFH : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PFH TitsMF.M

end CertificateChecks.KernelSporSch.TitsFive

end
