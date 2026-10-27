module

public import CFSG.Quasithin.Recognition.ModelBridgesJ3Inputs
public import Certificates.Kernel.Sporadic.RawGen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.J3S1 CFSG.Blueprint.NativeSporadic.J3Seed1
#ks_chars CertificateChecks.KernelMisc.J3S2 CFSG.Blueprint.NativeSporadic.J3Seed2
#ks_chars CertificateChecks.KernelMisc.J3D1 CFSG.Open.quasithinJ3Data1
#ks_chars CertificateChecks.KernelMisc.J3D2 CFSG.Open.quasithinJ3Data2

public section

namespace CertificateChecks.KernelMisc

open CFSG.Quasithin CFSG.Open CFSG.Blueprint.NativeSporadic

theorem j3_entries₁ : nativeModeOneEntries J3Seed1 = quasithinDigits quasithinJ3Data1 := by
  rw [J3S1.eq, J3D1.eq, nativeModeOneEntries, quasithinDigits, String.toList_ofList,
    String.toList_ofList]
  decide +kernel

theorem j3_entries₂ : nativeModeOneEntries J3Seed2 = quasithinDigits quasithinJ3Data2 := by
  rw [J3S2.eq, J3D2.eq, nativeModeOneEntries, quasithinDigits, String.toList_ofList,
    String.toList_ofList]
  decide +kernel

end CertificateChecks.KernelMisc

end
