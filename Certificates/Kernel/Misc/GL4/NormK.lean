module

public import Certificates.Data.Kernel.Misc.A5Norm
public import Certificates.Data.A5GL42Norm

public section

namespace CertificateChecks.KernelMisc.A5Norm

open CFSG.KD.A5Norm Certificates.A5GL42

theorem compN : withP (compC codesN codesNHN 8580 32306) = true := by decide +kernel
theorem compO : withP (compC codesO codesNHO 18479 9240) = true := by decide +kernel
theorem centN : withP (centC 8580 32306) = true := by decide +kernel
theorem centO : withP (centC 18479 9240) = true := by decide +kernel
theorem grpNHN : grpC codesNHN = true := by decide +kernel
theorem grpNHO : grpC codesNHO = true := by decide +kernel
theorem grpT0N : grpC codesT0N = true := by decide +kernel
theorem grpT0O : grpC codesT0O = true := by decide +kernel
theorem subT0N : subC codesT0N codesNHN = true := by decide +kernel
theorem subT0O : subC codesT0O codesNHO = true := by decide +kernel
theorem freeN : freeC codesNHN codesT0N = true := by decide +kernel
theorem freeO : freeC codesNHO codesT0O = true := by decide +kernel
theorem fixN : fixC 8580 32306 = true := by decide +kernel
theorem fixO : fixC 18479 9240 = true := by decide +kernel
theorem trans1 : transC codesO [1, 2, 3, 4, 5, 6, 8, 9, 10, 12] 1 = true := by decide +kernel
theorem trans2 : transC codesO [7, 11, 13, 14, 15] 7 = true := by decide +kernel

end CertificateChecks.KernelMisc.A5Norm

end
