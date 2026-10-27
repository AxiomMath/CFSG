module

public import Certificates.Kernel.UnitarySix.Sec3.E3600Chk
public import Certificates.Kernel.UnitarySix.Sec3.Chains3600
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

theorem wK_spec {w : List ℕ} (hw : ∀ k ∈ w, k < 18) :
    wA w = unpack 693 10 (wK w) ∧ canonK 693 10 (mask 10) (693 * 10) (wK w) = true :=
  wA_unpack hG hc hid hidA w hw

section

variable {X : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true)
include hX

theorem conj_canon {g gi : ℕ} (hg : PermK g gi = true) :
    canonK 693 10 (mask 10) (693 * 10) (pcomp 693 10 (mask 10) g (pcomp 693 10 (mask 10) X gi)) =
      true :=
  canon_comp (PermK.canon hg) (canon_comp hX (PermK.canon_inv hg))

theorem eq_id : eqA 693 (unpack 693 10 X) (idA 693) = Nat.beq X (pidn 693 10) := by
  rw [hidA, eq_unpack hX hid]

theorem wconj {w : List ℕ} (hw : ∀ k ∈ w, k < 18) (hp : PermK (wK w) (wKI w) = true) :
    conjA 693 (wA w) (unpack 693 10 X) =
      unpack 693 10 (pcomp 693 10 (mask 10) (wK w) (pcomp 693 10 (mask 10) X (wKI w))) := by
  rw [(wK_spec hw).1, conj_unpack hp hX]

end

end CertificateChecks.KernelU6.Sec3
