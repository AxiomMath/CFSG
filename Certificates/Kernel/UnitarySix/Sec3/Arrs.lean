module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Data

public section

namespace CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

@[expose] def sS : Array (Array Nat) := chS.S
@[expose] def bS : Array Nat := chS.B
@[expose] def dS : List (List Int) := chS.words
@[expose] def sX1 : Array (Array Nat) := chX1.S
@[expose] def bX1 : Array Nat := chX1.B
@[expose] def dX1 : List (List Int) := chX1.words
@[expose] def sX2 : Array (Array Nat) := chX2.S
@[expose] def bX2 : Array Nat := chX2.B
@[expose] def dX2 : List (List Int) := chX2.words
@[expose] def sX3 : Array (Array Nat) := chX3.S
@[expose] def bX3 : Array Nat := chX3.B
@[expose] def dX3 : List (List Int) := chX3.words
@[expose] def sK1 : Array (Array Nat) := chK1.S
@[expose] def bK1 : Array Nat := chK1.B
@[expose] def dK1 : List (List Int) := chK1.words
@[expose] def sK2 : Array (Array Nat) := chK2.S
@[expose] def bK2 : Array Nat := chK2.B
@[expose] def dK2 : List (List Int) := chK2.words
@[expose] def sA1 : Array (Array Nat) := chA1.S
@[expose] def bA1 : Array Nat := chA1.B
@[expose] def dA1 : List (List Int) := chA1.words
@[expose] def sA2 : Array (Array Nat) := chA2.S
@[expose] def bA2 : Array Nat := chA2.B
@[expose] def dA2 : List (List Int) := chA2.words
@[expose] def sK1A1 : Array (Array Nat) := chK1A1.S
@[expose] def bK1A1 : Array Nat := chK1A1.B
@[expose] def dK1A1 : List (List Int) := chK1A1.words
@[expose] def sK2A2 : Array (Array Nat) := chK2A2.S
@[expose] def bK2A2 : Array Nat := chK2A2.B
@[expose] def dK2A2 : List (List Int) := chK2A2.words
@[expose] def sL : Array (Array Nat) := chL.S
@[expose] def bL : Array Nat := chL.B
@[expose] def dL : List (List Int) := chL.words
@[expose] def sB12 : Array (Array Nat) := chB12.S
@[expose] def bB12 : Array Nat := chB12.B
@[expose] def dB12 : List (List Int) := chB12.words
@[expose] def sB23 : Array (Array Nat) := chB23.S
@[expose] def bB23 : Array Nat := chB23.B
@[expose] def dB23 : List (List Int) := chB23.words
@[expose] def sSJ : Array (Array Nat) := chSJ.S
@[expose] def bSJ : Array Nat := chSJ.B
@[expose] def dSJ : List (List Int) := chSJ.words
@[expose] def sT1 : Array (Array Nat) := chT1.S
@[expose] def bT1 : Array Nat := chT1.B
@[expose] def dT1 : List (List Int) := chT1.words
@[expose] def sT2 : Array (Array Nat) := chT2.S
@[expose] def bT2 : Array Nat := chT2.B
@[expose] def dT2 : List (List Int) := chT2.words

end CertificateChecks.KernelU6.Sec3
