module

public import Certificates.Kernel.SporSch.HN.T0Data
public import Certificates.Data.Kernel.SporSch.HNT0P
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KD.HNT0 CFSG.KS.HNT0 CFSG.KS.EnumBase

#kc_each CertificateChecks.KernelSporSch.HNT0 ch10509a
  (fun s => sliceK 687 8 (adjK 687 8 255 BP 24 IL AL PR KB) s) 0 43

theorem neg_adj : Bool.not (adjK 687 8 255 BP 24 IL (fun a => Nat.xor (AL a) 2) PR KB 0) = true :=
  by quickRfl
theorem neg_adjh : Bool.not (adjK 687 8 255 BP 24 IL
    (fun a => Nat.xor (AL a) (Nat.shiftLeft 1 1025)) PR KB 0) = true := by quickRfl
theorem neg_adjz : Bool.not (adjK 687 8 255 BP 24 IL
    (fun a => Nat.lor (AL a) (Nat.shiftLeft 1 700)) PR KB 0) = true := by quickRfl
theorem neg_pr : Bool.not (adjK 687 8 255 BP 24 IL AL (fun a => Nat.xor (PR a) 1024) KB 0) =
    true := by quickRfl
theorem neg_prT : Bool.not (adjK 687 8 255 BP 24 IL AL (fun a => PR (Nat.succ a)) KB 0) = true :=
  by quickRfl

end CertificateChecks.KernelSporSch.HNT0

end
