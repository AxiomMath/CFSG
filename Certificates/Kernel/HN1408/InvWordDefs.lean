module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
public import Certificates.Kernel.HN1408.Words

public section

namespace CFSG.KD.HN1408.CzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def wordG (G0 G1 : Nat) (w : List Nat) : Nat :=
  wfoldK 1408 11 (mask 11) (fun l => nIf(Nat.beq l 0, G0, G1)) w idK

@[expose] def u1W : List Nat := [0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]

@[expose] def u2W : List Nat := [0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0]

@[expose] def aW : List Nat := [0, 0, 0, 0, 0, 0, 0]

@[expose] def bW : List Nat := [1, 1, 1, 1, 1, 1, 1]

@[expose] noncomputable def wordsInK (gs hs : List (List Nat)) (w0 w1 : List Nat) : Bool :=
  strictB (WK (gs.getD 0 [])) fun G0 => strictB (WK (gs.getD 1 [])) fun G1 =>
    bAnd(Nat.beq (wordG G0 G1 w0) (WK (hs.getD 0 [])), Nat.beq (wordG G0 G1 w1) (WK (hs.getD 1 [])))

@[expose] noncomputable def azWordsK : Bool := wordsInK classaz.centGens classz.centGens u1W u2W

@[expose] noncomputable def bWordsK : Bool := wordsInK classb.centGens [wordA, wordB] aW bW

end CFSG.KD.HN1408.CzInv

end
