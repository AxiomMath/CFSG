module

public import Certificates.Kernel.OmegaEight.Pi416101S

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8

theorem q8Part3_0 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 3 && k % 3 == 0).dedup) = true := by
  decide +kernel

theorem q8Part3_1 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 3 && k % 3 == 1).dedup) = true := by
  decide +kernel

theorem q8Part3_2 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 3 && k % 3 == 2).dedup) = true := by
  decide +kernel

theorem q8Part3 : q8Part (nat_lit 3) = true :=
  q8_split 3 3 (by decide) fun j hj => match j, hj with
    | 0, _ => q8Part3_0
    | 1, _ => q8Part3_1
    | 2, _ => q8Part3_2
    | _ + 3, h => absurd h (by omega)

end CertificateChecks.KernelO8

end
