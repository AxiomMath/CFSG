module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSLitData
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

public section

namespace CFSG.KD.LQT.H4089

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Vol2Native.L239.HSPairs

def idT : Array Nat := Array.range 1100

def powT (t : Array Nat) : Nat → Array Nat
  | 0 => idT
  | k + 1 => compArr t (powT t k)

def letT (w : List Nat) : Array (Array Nat) :=
  (hsQp.map fun p => hsSLP[p.1]!).toArray ++ #[wordTabA #[hsTa, hsTb] 1100 w]

def qtT (L : Array (Array Nat)) (w : List Nat) (k : Nat) : Array Nat :=
  powT (wordTabA L 1100 w) k

def commT (a b c d : Array Nat) : Array Nat := compArr (compArr (compArr a b) c) d

def cpT : Array (Array Nat) :=
  let L1 := letT hsW1
  let L2 := letT hsW2
  let b1 := qtT L1 [3, 3] 1
  let b1i := powT b1 2
  let x1 := qtT L1 [0] 1
  let y1 := qtT L1 [2, 0, 2] 1
  let b2 := qtT L2 [3, 3, 1] 2
  let b2i := powT b2 2
  let x2 := qtT L2 [2, 1, 0, 1] 1
  let x2i := powT x2 3
  let y2 := qtT L2 [2, 2] 1
  #[idT, L1[3]!, L2[3]!, b1, b1i, x1, x1, y1, y1, commT x1 b1 x1 b1i, commT y1 b1 y1 b1i,
    qtT L1 [3, 1, 2, 1] 2, b2, b2i, x2, x2i, y2, y2, commT x2 b2 x2i b2i, commT y2 b2 y2 b2i,
    qtT L2 [3] 1]

def cpQp : List (Nat × Nat) := []

end CFSG.KD.LQT.H4089

end
