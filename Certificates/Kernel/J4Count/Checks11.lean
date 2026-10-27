module

public import Certificates.Data.Kernel.J4Slp
public import Certificates.Kernel.J4Q.MatData
public import CFSG.Sporadic.Schreier.J4SData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.KC.J4Q CFSG.KC.J4Slp CFSG.KD.J4Q CFSG.KS.SporSch.J4B

@[expose] noncomputable def R11 : List Nat := runK c rm one max7Codes (initK one A A B Bi)

@[expose] noncomputable def P1K : Nat :=
  vecJ rm CFSG.Sporadic.J4Schreier.rootBits (wFK c rm one A A B Bi wordP1 one)

theorem fix11 : chk11 c rm one P1K R11 = true := by quickRfl

theorem p1_lt : Nat.blt P1K (Nat.pow 2 112) = true := by quickRfl

end CertificateChecks.KernelJ4Count

end
