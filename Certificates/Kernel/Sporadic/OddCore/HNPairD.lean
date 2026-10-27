module

public import CFSG.RankThree.PartOne.S11c.HNInvPairInputs
meta import CFSG.RankThree.PartOne.S11c.HNInvPairInputs

public section

namespace CertificateChecks.KernelSpor.HNPair

open CFSG.RankThree.PartOne.HNRed.Native CFSG.Sporadic.HNOddCore

meta def pM : Array (Array Nat) := #[pairA, pairB]
meta def sM : Array (Array Nat) := strongArrs 1200 pM SixData.dWords
meta def bM : Array Nat := (pairBase.map Fin.val).toArray

@[expose] def dD : List (List Int) := (SixData.dWords.extract 2 SixData.dWords.size).toList

end CertificateChecks.KernelSpor.HNPair

end
