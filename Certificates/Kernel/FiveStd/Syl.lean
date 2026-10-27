module

public import Certificates.Kernel.FiveStd.ClsData
public import Certificates.Data.Kernel.FiveStdKSyl
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

@[expose] def W5 : Nat :=
  102247792626102923526576089927524417226212643261441496955368001975975850148249919614414809205414573350636247130116

@[expose] def W3 : Nat := 64551619450433101657927118056966275076

theorem syl5 : sylOK OR OM 5 29501 78797 5 W5 = true := by quickRfl

theorem syl3 : sylOK OR OM 5 30751 78799 3 W3 = true := by quickRfl

end CertificateChecks.FiveStd

end
