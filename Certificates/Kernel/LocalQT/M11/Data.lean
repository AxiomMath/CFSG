module

public import Certificates.Data.Kernel.LocalQT.M11
public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.Sporadic.Mathieu.M11
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Certificates.Certificate113

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.M11

open CFSG.KC.LQT.M

@[expose] def CA : Nat := 3420860021279008
@[expose] def CB : Nat := 11576764645055619
@[expose] def R1 : List Nat := [11584701642934304, 2401579492812801, 11580166027575458, 11576764645055619, 8058329520744548, 285977387182149, 9193024371363142, 11581231272561927, 3418454875973864, 2470883009825801, 3422784232431818]
@[expose] def R2 : List Nat := [0, 11584701642934304, 11299962429345856, 11298793251446880, 5949700358603904, 4549988806002848, 5675956287153344, 1451495046452448, 10176188759807232, 3420860021279008, 3701099217329472]
@[expose] def R3 : List Nat := [0, 0, 11584701642934304, 11336279631563808, 7960645754753056, 4791915751183392, 5779138687506464, 11370123032304672, 10245389174513696, 3597950175585312, 5953035233732640]
@[expose] def R4 : List Nat := [0, 0, 0, 11584701642934304, 8064170770696224, 6872230211520544, 10382864738879520, 3664819570051104, 5986054001920032, 9155850326542368, 4724710188582944]
@[expose] def W1 : List (List Nat) := [[], [1, 0, 1, 1, 1], [1, 1], [1], [1, 1, 0, 1, 1, 1], [1, 1, 1, 0, 1, 1, 1], [0, 1, 1, 0, 1, 1, 1], [1, 1, 1], [0, 1, 1, 1], [0, 1, 0, 1, 1, 1], [0, 1]]
@[expose] def W2 : List (List Nat) := [[], [], [1, 1, 1, 0, 1, 1, 1, 0, 1, 0], [1, 1, 0, 1, 0, 1, 1, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0], [1, 1, 1, 0, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 0, 1, 0, 1, 0], [0], [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]]
@[expose] def W3 : List (List Nat) := [[], [], [], [1, 1, 0, 1, 0, 1, 1, 1, 0, 1], [1, 1, 1, 0, 1, 1, 1, 0, 1], [1, 1, 0, 1, 0, 1, 0, 1], [1, 1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1], [1, 1, 0, 1, 0, 1, 1, 0, 1], [1, 1, 1, 0, 1, 0, 1], [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]]
@[expose] def W4 : List (List Nat) := [[], [], [], [], [1, 1, 0, 1, 1], [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1], [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1]]

theorem ha : CFSG.KC.LQT.S.code CFSG.Sporadic.Mathieu.m11gA = CA := by decide +kernel
theorem hb : CFSG.KC.LQT.S.code CFSG.Sporadic.Mathieu.m11gB = CB := by decide +kernel
theorem hg : grpM CA CB R1 R2 R3 R4 W1 W2 W3 W4 = true := by quickRfl

end CFSG.KD.LQT.M11

end
