module

public import Certificates.Data.CatFactsL4U4P1L43Data

public section

namespace CertificateChecks.KernelP1L43

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def e (k : ℕ) (ε : Bool) : Array ℕ := tab80 k ε

@[expose] def ps : List ℕ := [0, 1, 2, 3, 4, 9, 40, 41, 42, 43, 44, 49]

@[expose] def ps6 : List ℕ := [0, 1, 2, 3, 4, 5]

@[expose] def gAB : Array (Array ℕ) := #[e codeA false, e codeB false]

@[expose] def rD0 : Array ℕ := e 11821474 false
@[expose] def rD1 : Array ℕ := e 14650228 false
@[expose] def rD2 : Array ℕ := e 38855539 false
@[expose] def rS0 : Array ℕ := e 40942156 false
@[expose] def rS1 : Array ℕ := e 6629227 true
@[expose] def rS2 : Array ℕ := e 28874841 false
@[expose] def rS3 : Array ℕ := e 12439050 true
@[expose] def rS4 : Array ℕ := e 12940497 true
@[expose] def rDS0 : Array ℕ := e 28777033 false
@[expose] def rDS1 : Array ℕ := e 12703935 false
@[expose] def rDS2 : Array ℕ := e 7174611 true

@[expose] def sylD : Array (Array ℕ) :=
  #[e 11821474 false, e 35176627 false, e 14650228 false, e 38855539 false]
@[expose] def sylS : Array (Array ℕ) :=
  #[e 40942156 false, e 6629227 true, e 28874841 false, e 33541807 false, e 38086032 true,
    e 9694318 false]
@[expose] def sylDS : Array (Array ℕ) :=
  #[e 28777033 false, e 12703935 false, e 8563353 false, e 40509289 true, e 7174611 true]

@[expose] def cD0 : Array (Array ℕ) := #[e 10394616 false, e 17819842 false]
@[expose] def cD1 : Array (Array ℕ) := #[e 15481057 false, e 42492655 false]
@[expose] def cD2 : Array (Array ℕ) := #[e 34288414 false, e 37099471 false]
@[expose] def cS0 : Array (Array ℕ) := #[e 6388611 false, e 11307727 false]
@[expose] def cS1 : Array (Array ℕ) := #[e 16162266 false, e 37212132 false]
@[expose] def cS2 : Array (Array ℕ) := #[e 23277730 false, e 40696764 false]
@[expose] def cS3 : Array (Array ℕ) := #[e 39850015 false, e 22163176 false]
@[expose] def cS4 : Array (Array ℕ) := #[e 15086220 false, e 39271333 false]
@[expose] def cDS0 : Array (Array ℕ) := #[e 8629557 false, e 8883729 false]
@[expose] def cDS1 : Array (Array ℕ) := #[e 19240684 false, e 32466360 false]
@[expose] def cDS2 : Array (Array ℕ) := #[e 1288381 false, e 660594 false]

@[expose] def kD2 : Array (Array ℕ) := #[e 18085123 false, e 27169507 false]
@[expose] def fS3 : Array (Array ℕ) := #[e 17897863 false, e 17928943 false]
@[expose] def fS4 : Array (Array ℕ) := #[e 2221498 false, e 41267271 false]
@[expose] def lD0 : Array (Array ℕ) := #[e 22222087 false, e 30806896 false]
@[expose] def lDS2 : Array (Array ℕ) := #[e 28947042 false, e 5634355 false]
@[expose] def dD0 : Array (Array ℕ) :=
  #[natArr (diagT 80 (tm 22222087) a6a), natArr (diagT 80 (tm 30806896) a6b)]
@[expose] def dDS2 : Array (Array ℕ) :=
  #[natArr (diagT 80 (tm 28947042) a6a), natArr (diagT 80 (tm 5634355) a6b)]
@[expose] def a6g : Array (Array ℕ) := #[natArr a6a, natArr a6b]

@[expose] def tD00 : Array (Array ℕ) :=
  #[e 19250470 false, e 30430192 false, e 30689447 false, e 9264380 false, e 20255771 false,
    e 37749583 false]
@[expose] def tD01 : Array (Array ℕ) :=
  #[e 19250470 false, e 30430192 false, e 30689447 false, e 22698403 false, e 9264380 false,
    e 36466306 false, e 20255771 false]
@[expose] def tD02 : Array (Array ℕ) :=
  #[e 19250470 false, e 30430192 false, e 30689447 false, e 9264380 false, e 20255771 false,
    e 37749583 false, e 27696302 true]
@[expose] def tD03 : Array (Array ℕ) :=
  #[e 19250470 false, e 30430192 false, e 30689447 false, e 9264380 false, e 20255771 false,
    e 37749583 false, e 4944412 true]
@[expose] def tDS20 : Array (Array ℕ) := #[e 8523990 false, e 17636468 false]
@[expose] def tDS21 : Array (Array ℕ) :=
  #[e 17636455 false, e 19250485 false, e 17637922 false, e 19250462 false, e 5354544 false]
@[expose] def tDS22 : Array (Array ℕ) :=
  #[e 17637922 false, e 20864225 false, e 8523990 false, e 31393781 true]
@[expose] def tDS23 : Array (Array ℕ) :=
  #[e 17637922 false, e 20864225 false, e 8523990 false, e 35872108 true]

end CertificateChecks.KernelP1L43

end
