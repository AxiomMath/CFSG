module

public import CFSG.Sporadic.FischerOddCore.Fi22CentData
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentText
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays

public section

namespace CertificateChecks.KernelSpor.Fi22H

open CFSG.Sporadic.FischerOddCore

meta def bytes : ByteArray := (fi22CentP0 ++ fi22CentP1 ++ fi22CentP2 ++ fi22CentP3).toUTF8

meta def S (c : Nat) : Array (Array Nat) :=
  Array.ofFn (n := [19, 16, 9, 19, 16].getD c 0) fun j =>
    CFSG.Monster.B.Fischer.hexLine bytes 3 3510 ([0, 19, 35, 44, 63].getD c 0 + j.val)

meta def S0 : Array (Array Nat) := S 0
meta def S1 : Array (Array Nat) := S 1
meta def S2 : Array (Array Nat) := S 2
meta def S3 : Array (Array Nat) := S 3
meta def S4 : Array (Array Nat) := S 4

meta def B : Array Nat := #[0, 1, 2, 3, 6, 4]

@[expose] def D0 : List (List Int) := fi22CentDerivations.getD 0 []
@[expose] def D1 : List (List Int) := fi22CentDerivations.getD 1 []
@[expose] def D2 : List (List Int) := fi22CentDerivations.getD 2 []
@[expose] def D3 : List (List Int) := fi22CentDerivations.getD 3 []
@[expose] def D4 : List (List Int) := fi22CentDerivations.getD 4 []

end CertificateChecks.KernelSpor.Fi22H

end
