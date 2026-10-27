module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixData

public section

namespace CFSG.KD.HN1408.FixR

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def h5aWord : List Nat := [2, 3, 6, 7, 2, 3, 7]

@[expose] def cent5aW : List (List Nat) := fix5A.cent.map fun c => h5aWord ++ c ++ h5aWord.reverse

@[expose] def rep5aW : List Nat := h5aWord ++ fix5A.rep ++ h5aWord.reverse

end CFSG.KD.HN1408.FixR

end
