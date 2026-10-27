module

public import Certificates.Kernel.SporSch.Ly.Seven2189
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.UInt.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.LySchreier.Native CertificateChecks.KernelSporSch

theorem rootChecks : bpRootChecks () = true := by
  unfold bpRootChecks
  rw [LySvF.key_eq, LySvD.keyD_eq]
  decide +kernel

end CertificateChecks.KernelLy

end
