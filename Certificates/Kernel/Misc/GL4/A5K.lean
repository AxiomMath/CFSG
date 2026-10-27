module

public import Certificates.Data.Kernel.Misc.GL4Grp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.GL4A5

open CFSG.KC.Misc.GL4 Certificates.A5GL42

theorem subC : SubC := by decide +kernel

theorem xorC : ∀ x < 16, ∀ u < 16, vecOfCode (x ^^^ u) = vecOfCode x + vecOfCode u := by
  decide +kernel

theorem grpN : GrpC codesN 8580 32306 := by decide +kernel

theorem grpO : GrpC codesO 18479 9240 := by decide +kernel

theorem gensC : ofCode 8580 = aN ∧ ofCode 32306 = bN ∧ ofCode 18479 = aO ∧ ofCode 9240 = bO := by
  decide +kernel

theorem fixN : FixN := by decide +kernel

theorem fixO : FixO := by decide +kernel

end CertificateChecks.KernelMisc.GL4A5

end
