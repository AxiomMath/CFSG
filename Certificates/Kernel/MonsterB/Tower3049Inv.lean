module

public import Certificates.Kernel.MonsterB.Tower3049Data
public import CFSG.Certificates.Kernel.Co1F2Sound
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Cover
public import Mathlib.Tactic.NormNum

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Tower3049

open CFSG.Monster.B.Max2.Native CFSG.KC.Co1F2

theorem inv_chk : ∀ j < 5282, bIf(Nat.beq (DA j) 3,
    inv22 (unpackR 22 (Certificates.Tw3049T (DB j))) ==
      unpackR 22 (Certificates.Tw3049T j), true) = true := by
  kc_cover 64

theorem inv_ok : ∀ j < 5282, DA j = 3 →
    inv22 (unpackR 22 (Certificates.Tw3049T (DB j))) = unpackR 22 (Certificates.Tw3049T j) := by
  intro j hj e
  have h := inv_chk j hj
  rw [e, Nat.beq_refl] at h
  exact beq_iff_eq.1 h

end CertificateChecks.Tower3049

end
