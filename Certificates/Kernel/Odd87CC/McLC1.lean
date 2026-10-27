module

public import Certificates.Data.Kernel.Odd87CCK
public import Certificates.Data.Odd87F3McL
public import Certificates.Kernel.LocalComp.McLCent
import CFSG.Certificates.Kernel.Odd87WordsText

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelOdd87CC.McLC1

open Certificates.Odd87F3 CFSG.KC.Odd87CCK CertificateChecks.KernelLC.McLC

@[expose] noncomputable def gens : List Nat := [MC.F 18, MC.F 19, MC.F 20, MC.F 21]

theorem chk : ccK 275 9 gens McL.orbs McL.cov = true := by
  simp only [McL.orbs, McL.orb0, McL.orb1, McL.orb2, McL.orb3, McL.cov, decodeWords_eq,
    decodeCov_eq, String.toList_append]
  decide +kernel

end CertificateChecks.KernelOdd87CC.McLC1
