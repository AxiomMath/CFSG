module

public import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.Sporadic.SmallOddCore

set_option maxRecDepth 400000 in
theorem sizes_sums : ∀ U : Finset (Fin 14), 0 ∈ U → (∑ l ∈ U, mclXSizes.getD l 0) ∣ 20160 →
    U = {0} ∨ U = Finset.univ := by
  decide +kernel

end CertificateChecks.KernelSpor.McL2287

end
