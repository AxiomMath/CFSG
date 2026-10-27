module

public import Certificates.Kernel.PropA.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28X

public section

namespace CertificateChecks.KernelPropA

open CFSG.EvenSporadicStandard.M12Std.PropA

theorem pa450010_x_eq : pa450010x = x28 := by
  unfold pa450010x x28
  have hw : pa450010wx = Data.wx0 := rfl
  rw [hw]
  exact wordP_congr le_rfl (fun l hl => by interval_cases l <;> simp [pa450010gK, ggD])
    (by decide +kernel)

end CertificateChecks.KernelPropA
