module

public import Certificates.Data.Kernel.L34DCShape

public section

namespace Certificates.L34DC

open Certificates.L34DC

theorem checkShape5167_ok : checkShape5167 = true := by decide +kernel

theorem wordsOK5167_ok : wordsOK () = true := by decide +kernel

end Certificates.L34DC
