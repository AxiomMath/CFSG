module

public import Certificates.Kernel.OmegaEight.Pi416101S

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8

theorem q8Part1_0 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 0).dedup) = true := by
  decide +kernel

theorem q8Part1_1 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 1).dedup) = true := by
  decide +kernel

theorem q8Part1_2 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 2).dedup) = true := by
  decide +kernel

theorem q8Part1_3 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 3).dedup) = true := by
  decide +kernel

theorem q8Part1_4_0 : q8ChunkLx piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 4).dedup) 6 0 = true := by
  decide +kernel

theorem q8Part1_4_1 : q8ChunkLx piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 4).dedup) 6 1 = true := by
  decide +kernel

theorem q8Part1_4_2 : q8ChunkLx piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 4).dedup) 6 2 = true := by
  decide +kernel

theorem q8Part1_4_3 : q8ChunkLx piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 4).dedup) 6 3 = true := by
  decide +kernel

theorem q8Part1_4_4 : q8ChunkLx piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 4).dedup) 6 4 = true := by
  decide +kernel

theorem q8Part1_4_5 : q8ChunkLx piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 4).dedup) 6 5 = true := by
  decide +kernel

theorem q8Part1_4 : q8ChunkL piSqL
    (((piSqL.map kNat).filter fun k => k % 8 == 1 && k % 5 == 4).dedup) = true :=
  q8ChunkL_of_x _ _ 6 (by decide) fun t ht => match t, ht with
    | 0, _ => q8Part1_4_0
    | 1, _ => q8Part1_4_1
    | 2, _ => q8Part1_4_2
    | 3, _ => q8Part1_4_3
    | 4, _ => q8Part1_4_4
    | 5, _ => q8Part1_4_5
    | _ + 6, h => absurd h (by omega)

theorem q8Part1 : q8Part (nat_lit 1) = true :=
  q8_split 1 5 (by decide) fun j hj => match j, hj with
    | 0, _ => q8Part1_0
    | 1, _ => q8Part1_1
    | 2, _ => q8Part1_2
    | 3, _ => q8Part1_3
    | 4, _ => q8Part1_4
    | _ + 5, h => absurd h (by omega)

end CertificateChecks.KernelO8

end
