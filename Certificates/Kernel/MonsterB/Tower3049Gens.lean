module

public import Certificates.Kernel.MonsterB.Tower3049Data
public import CFSG.Certificates.Kernel.Co1F2Sound
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Tower3049

open CFSG.Monster.B.Max2.Native CFSG.KC.Co1F2

theorem r1_eq : r1Rows = unpackR 22 (Certificates.Tw3049T 1) := by decide +kernel

theorem r2_eq : r2Rows = unpackR 22 (Certificates.Tw3049T 2) := by decide +kernel

theorem gens_ok : gensOK () = true := by decide +kernel

theorem shape_ok : shapeOK () = true := by decide +kernel

end CertificateChecks.Tower3049

end
