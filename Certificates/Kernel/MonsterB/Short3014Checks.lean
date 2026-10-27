module

public import Certificates.Kernel.MonsterB.Short3014Data
public import Certificates.Data.CFSGNative.MonsterVis.Frame
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Short3014

open CFSG.KLie.CT CFSG.Monster.VisCert.Native

set_option maxRecDepth 100000

theorem fr_ok : allN 15 (fun g => allN 24 fun t =>
    Nat.beq (fget FR (Nat.add (Nat.mul 24 g) t) 24) (frameRows[g]!)[t]!) = true := by
  decide +kernel

theorem t0 : slice 0 6 = true := by quickRfl
theorem t1 : slice 6 6 = true := by quickRfl
theorem t2 : slice 12 6 = true := by quickRfl
theorem t3 : slice 18 6 = true := by quickRfl
theorem t4 : slice 24 6 = true := by quickRfl
theorem t5 : slice 30 6 = true := by quickRfl
theorem t6 : slice 36 6 = true := by quickRfl
theorem t7 : slice 42 6 = true := by quickRfl

end CertificateChecks.Short3014

end
