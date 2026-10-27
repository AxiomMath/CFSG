module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Data

public section

namespace CFSG.KD.HN1408

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def vYI : List Nat := [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0]

@[expose] def vWordYI : List Nat := vYI.flatMap fun l => if l = 0 then y0Word else i0Word

end CFSG.KD.HN1408

end
