module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeInputs

public section

namespace CFSG.KD.SuzThree13637

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

@[expose] def qA0 : Array Nat := (qGensS ())[0]!

@[expose] def qA1 : Array Nat := (qGensS ())[1]!

@[expose] def qA2 : Array Nat := (qGensS ())[2]!

@[expose] def cGs : Array (Array Nat) := cGens (levels ())

@[expose] def cKeysA : Array Nat := cKeys.toArray

end CFSG.KD.SuzThree13637

end
