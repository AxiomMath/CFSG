module

public import Certificates.Kernel.SporSch.Ly.PermQ

public section

namespace CertificateChecks.KernelSporSch.LyPerm

theorem q0 : QStmt 0 := by unfold QStmt; decide +kernel
theorem q1 : QStmt 1 := by unfold QStmt; decide +kernel
theorem q2 : QStmt 2 := by unfold QStmt; decide +kernel

end CertificateChecks.KernelSporSch.LyPerm

end
