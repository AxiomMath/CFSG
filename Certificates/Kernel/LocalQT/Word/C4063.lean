module

public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23BaseInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.Defs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4063

open CFSG.KC.LQT.W CFSG.QuasithinUnique.A5.G3.M23

@[expose] def cA : List Nat := [29396287020561317414859794500619265, 4436007312844787929641103698034959]
@[expose] def cT : List Nat := [16453652227586117563161294244186208, 28178097059690613567447096695570560, 16453638129065538717347888777052704, 20023356628447128124161733648132352]
@[expose] def c1 : List Nat := [28783686814883616497404740355012992, 14503677819134255209500979729867232]
@[expose] def c2 : List Nat := [29069304957762462340378035758663840, 2621032705298783971649977188391464]
@[expose] def wT : List (List Nat) :=
  [[0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0], [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0]]
@[expose] def w1 : List (List Nat) := [[1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1]]
@[expose] def w2 : List (List Nat) := [[1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1], [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]]

theorem hA : natGens.map codeP = cA := by decide +kernel
theorem hT : tGens.map codeP = cT := by decide +kernel
theorem h1 : mGens1.map codeP = c1 := by decide +kernel
theorem h2 : mGens2.map codeP = c2 := by decide +kernel
theorem kT : wordsOK 23 cA cT wT = true := by quickRfl
theorem k1 : wordsOK 23 cA c1 w1 = true := by quickRfl
theorem k2 : wordsOK 23 cA c2 w2 = true := by quickRfl

end CFSG.KD.LQT.C4063

end
