module

public import Certificates.Kernel.Q8Wit.J3EnumK
public import Certificates.Kernel.Q8Wit.J3Data
public import Certificates.Kernel.Q8Wit.J3Data2
public import Certificates.Data.Kernel.Q8WitP2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.J3

open CFSG.KC.Enum (pidn)
open CFSG.KC.Q8Wit

theorem idJ : Nat.beq J3P2.ID (pidn 6156 13) = true := by quickRfl

theorem commJ : commTabK 6156 13 J3Q.N nc J3P2.nm SQ C J3P2.MK J3P2.MZ = true := by quickRfl

theorem freeJ : q8WitFreeP2 6156 13 J3Q.N J3P2.ID J3Q.T SQ J3P2.D J3P2.nm C CI J3P2.MK J3P2.MZ
    J3P2.R J3P2.RM RF RO RN = true := by
  quickRfl

end CertificateChecks.KernelQ8W.J3

end
