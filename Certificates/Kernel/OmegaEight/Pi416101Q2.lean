module

public import Certificates.Kernel.OmegaEight.Pi416101S

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8

theorem q8Part2_0 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 2 && k % 3 == 0).dedup) = true := by
  decide +kernel

theorem q8Part2_1 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 2 && k % 3 == 1).dedup) = true := by
  decide +kernel

theorem q8Part2_2 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 2 && k % 3 == 2).dedup) = true := by
  decide +kernel

theorem q8Part2 : q8Part (nat_lit 2) = true :=
  q8_split 2 3 (by decide) fun j hj => match j, hj with
    | 0, _ => q8Part2_0
    | 1, _ => q8Part2_1
    | 2, _ => q8Part2_2
    | _ + 3, h => absurd h (by omega)

end CertificateChecks.KernelO8

end
