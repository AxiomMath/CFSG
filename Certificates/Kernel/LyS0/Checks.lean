module

public import Certificates.Kernel.LyS0.Data
public import Certificates.Data.Kernel.LyS0.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyS0

open CFSG.KD.LyS0

theorem pOps : parseOK (opsRec T) OS.chars 1490 = true := by quickRfl

theorem pPar : parseOK (parRec T) PS.chars 4374 = true := by quickRfl

theorem pL : parseOK (LRec T) LS.chars 10935 = true := by quickRfl

theorem shape : shapeK T = true := by quickRfl

theorem opsB : opsK T = true := by quickRfl

theorem kill : killK T = true := by quickRfl

end CertificateChecks.KernelLyS0

end
