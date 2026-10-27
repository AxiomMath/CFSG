module

public import Certificates.Kernel.TwoHS.HY
public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native

@[expose] noncomputable def L (l : Nat) : Nat := HY.F (l - 1)

@[expose] noncomputable def idK : Nat := pidn 11200 14

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 11200 14 (mask 14) p q

@[expose] noncomputable def WK (wd : List Nat) : Nat := wfoldK 11200 14 (mask 14) L wd idK

@[expose] noncomputable def UL (l : Nat) : Nat := WK (harUW.getD (l - 1) [])

@[expose] noncomputable def UK (wd : List Nat) : Nat := wfoldK 11200 14 (mask 14) UL wd idK

@[expose] def lettersOK (wd : List Nat) : Bool := wd.all fun l => 1 ≤ l && l ≤ 6

@[expose] noncomputable def wEq (u v : List Nat) : Bool :=
  if (lettersOK u && lettersOK v) = true then Nat.beq (WK u) (WK v)
  else tblEq 11200 (wordTbl 11200 harYs u) (wordTbl 11200 harYs v)

end CFSG.KD.TwoHS

end
