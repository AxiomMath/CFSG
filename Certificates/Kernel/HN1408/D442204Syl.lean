module

public import Certificates.Kernel.HN1408.Y442202Defs
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalQT.PEnumD
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5DData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Letters
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5DData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Letters
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.D442204M

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.Simple2S5

meta def tabN (t : CFSG.Sporadic.Th.Native.Table) : Array Nat := t.map UInt32.toNat
meta def idM : Array Nat := idTab 1408
meta def wM (w : List Nat) : Array Nat := tabN (tabW w)
meta def mulM (p q : Array Nat) : Array Nat := comp 1408 p q
meta def subsM : Array (Array Nat) := #[wM (yWord 0 0), wM (yWord 0 1), wM (gWords.getD jStar [])]

meta def lwM (l : List Nat) : Array Nat := l.foldl (fun acc i => mulM acc subsM[i - 1]!) idM

meta def gensS (i : Nat) : Array (Array Nat) := ((sylowLetters.getD i []).map lwM).toArray
meta def gS7 : Array (Array Nat) := gensS 0
meta def gS9 : Array (Array Nat) := gensS 1
meta def gS125 : Array (Array Nat) := gensS 2
meta def ids1 : Array (Array Nat) := Array.replicate 1 idM
meta def ids2 : Array (Array Nat) := Array.replicate 2 idM

end CFSG.KD.HN1408.D442204M

open CFSG.KD.HN1408.D442204M in
#kmulh CFSG.KD.HN1408.D442204.S7 1408 11 gS7 ids1 idM 4096
open CFSG.KD.HN1408.D442204M in
#kmulh CFSG.KD.HN1408.D442204.S9 1408 11 gS9 ids2 idM 4096
open CFSG.KD.HN1408.D442204M in
#kmulh CFSG.KD.HN1408.D442204.S125 1408 11 gS125 ids2 idM 4096
