
module

public import CFSG.Sporadic.Schreier.J4SRankData

public section

namespace CertificateChecks.KernelSporSch.J4Rank

open CFSG.Sporadic.J4Schreier

@[expose] def q3Suf0 : Array Pair :=
  (Array.range 9).map fun k => wordP Xn Yn ((q3Words[0]!).drop (100 * k))

@[expose] def q3Suf1 : Array Pair :=
  (Array.range 9).map fun k => wordP Xn Yn ((q3Words[1]!).drop (100 * k))

@[expose] def q3Elts : Array Pair := (Array.range 27).map (q3PairK Q3GenPairs)

@[expose] def etaRows : Array Pair := #[etaP 1, etaP 14]

end CertificateChecks.KernelSporSch.J4Rank

end
