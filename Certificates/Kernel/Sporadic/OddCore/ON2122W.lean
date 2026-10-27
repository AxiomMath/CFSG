module

public import CFSG.Sporadic.ONOddCore.LiftGraphInputs

public section

namespace CertificateChecks.KernelSpor.ON2122

open CFSG.Sporadic.ONOddCore

@[expose] def resD : List (List Int) := (resW.extract 3 8).toList

@[expose] def resBA : Array Nat := #[0, 1, 2]

@[expose] def resWS : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1, 1, 1], [0], [1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1], [1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1]]

@[expose] def liftAt (k i : Nat) : LiftEntry := (localCert.records.getD k default).lifts.getD i default

def mS : Array (Array Nat) := CFSG.Sporadic.HNOddCore.strongArrs 480 resArrs resW

def pS (k i : Nat) : Array (Array Nat) :=
  CFSG.Sporadic.HNOddCore.strongArrs 960 (resPair (liftAt k i)) resW

def pS0_0 := pS 0 0
def pS0_1 := pS 0 1
def pS0_2 := pS 0 2
def pS0_3 := pS 0 3
def pS3_0 := pS 3 0
def pS3_1 := pS 3 1
def pS3_2 := pS 3 2
def pS3_3 := pS 3 3
def pS9_0 := pS 9 0
def pS9_1 := pS 9 1
def pS9_2 := pS 9 2
def pS9_3 := pS 9 3
def pS10_0 := pS 10 0
def pS10_1 := pS 10 1
def pS10_2 := pS 10 2
def pS10_3 := pS 10 3

end CertificateChecks.KernelSpor.ON2122

end
