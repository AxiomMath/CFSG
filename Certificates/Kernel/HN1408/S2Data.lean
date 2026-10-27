module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIData

public section

namespace CFSG.KD.HN1408

open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native

@[expose] def labsS2 : List Table := [#[6, 7, 0, 3, 5, 1, 4, 2], #[5, 0, 2, 7, 6, 4, 3, 1]]

@[expose] def blkData2S : BlkData where
  k := 8
  blk := blkData2.blk
  gens := sWords2
  labs := labsS2

@[expose] def orbS2 : List Nat := [3, 272, 323, 168, 202, 122, 356, 8]

end CFSG.KD.HN1408

end
