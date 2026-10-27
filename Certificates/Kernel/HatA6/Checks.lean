module

public import Certificates.Data.Kernel.HatA6K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHatA6

open CFSG.KC.HatA6 CFSG.Quasithin.H13.HatE CFSG.Quasithin.H13.HatC

@[expose] noncomputable def G0 : List Nat := g0List.map packL

theorem conj : conjOK = true := by decide +kernel

theorem g0wf : g0List.all (fun m => unpackL (packL m) == m) = true := by quickRfl

theorem g0len : g0List.length = 1080 := by decide +kernel

theorem g0 : g0R G0 = true := by quickRfl

theorem invS0 : invSliceR 0 8 = true := by quickRfl
theorem invS1 : invSliceR 8 8 = true := by quickRfl
theorem invS2 : invSliceR 16 8 = true := by quickRfl
theorem invS3 : invSliceR 24 8 = true := by quickRfl
theorem invS4 : invSliceR 32 8 = true := by quickRfl
theorem invS5 : invSliceR 40 8 = true := by quickRfl
theorem invS6 : invSliceR 48 8 = true := by quickRfl
theorem invS7 : invSliceR 56 8 = true := by quickRfl

theorem genS0 : genSliceR 0 8 = true := by quickRfl
theorem genS1 : genSliceR 8 8 = true := by quickRfl
theorem genS2 : genSliceR 16 8 = true := by quickRfl
theorem genS3 : genSliceR 24 8 = true := by quickRfl
theorem genS4 : genSliceR 32 8 = true := by quickRfl
theorem genS5 : genSliceR 40 8 = true := by quickRfl
theorem genS6 : genSliceR 48 8 = true := by quickRfl
theorem genS7 : genSliceR 56 8 = true := by quickRfl

end CertificateChecks.KernelHatA6

end
