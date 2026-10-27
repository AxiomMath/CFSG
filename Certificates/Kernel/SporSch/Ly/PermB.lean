module

public import Certificates.Kernel.SporSch.Ly.PermQ

public section

namespace CertificateChecks.KernelSporSch.LyPerm

theorem q3 : QStmt 3 := by unfold QStmt; decide +kernel
theorem q4 : QStmt 4 := by unfold QStmt; decide +kernel
theorem q5 : QStmt 5 := by unfold QStmt; decide +kernel

end CertificateChecks.KernelSporSch.LyPerm

end
