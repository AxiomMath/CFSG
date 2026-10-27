module

public import Certificates.Kernel.Sporadic.OddCore.J3OutSyl
public import Certificates.Kernel.Fin76bAut.Data
public import Certificates.Data.Kernel.Fin76bAut
public import Certificates.Data.Kernel.TC2Outer0
public import Certificates.Data.Kernel.Spor.RecMul
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.J3OutX25890

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.RecMul CFSG.KS.EAut CFSG.EvenSporadicStandard.Fin76b
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelFin76bAut (ET)

@[expose] def oddJ3 (l : Nat) : Bool := l == 3 || l == 6

@[expose] noncomputable def mulJ3K (a b : Nat) : Nat := mulRf 8 J3XS.POS J3XS.PL 5 a b

@[expose] noncomputable def innJ3K (a : Nat) : Bool := !oddRf J3XS.PL oddJ3 5 a

@[expose] def EL25890 : List ℕ :=
  [144, 184, 221, 225, 77, 54, 129, 134, 5, 12, 2, 9, 124, 86, 31, 178, 56, 131, 35, 62, 18, 41,
    105, 170, 94, 19, 13, 90, 38, 6, 0, 1]

@[expose] def SIG25890 : List ℕ :=
  [0, 144, 77, 184, 5, 54, 178, 105, 18, 12, 31, 170, 19, 56, 131, 221, 225, 90, 62, 38, 94, 1, 2,
    134, 9, 6, 13, 129, 35, 41, 86, 124]

@[expose] def WD25890 : List (List Int) :=
  [[1], [4, 3, 2, 1, -2, -3, 4], [2, 4, 2, 1, 5, -3, 2, -3, -5, -3, 4, 3, 3, -5],
    [3, 3, 5, 2, 1, -3, -2, 1, 5, -3, 5, 1, 3, 5], [3, 2, 1, -2, -3, -5, 3, 1, -3, 4, -5],
    [-5, 3, 1, -3, 4, -5], [3, 3, 5, 2, 1, -3, -2, 1, 3, 3, -5, 3, 5],
    [2, 3, 1, 2, 3, 1, 2, -3, -5, 3, 1, -5, 1, 5]]

@[expose] noncomputable def wdVal (j : Nat) : Nat :=
  if oddJ3 j then pcomp 6156 13 (mask 13) (J3CentP (j + 1)) (J3CentP 0) else J3CentP (j + 1)

@[expose] noncomputable def lab25890 : Bool :=
  (List.range 32).all (fun a => (List.range 32).all fun b =>
      SIG25890.getD (eMul ET a b) 0 == mulJ3K (SIG25890.getD a 0) (SIG25890.getD b 0)) &&
    SIG25890.all EL25890.contains && EL25890.all SIG25890.contains &&
    decide (SIG25890.length = 32) && decide SIG25890.Nodup &&
    SIG25890.getD 0 0 == 0 && SIG25890.getD 21 0 == 1

theorem kBase25890 : ((List.range 256).all fun b => reachRf J3XS.PL 5 b) &&
    Nat.beq (J3XS.T 1) (J3CentP 9) = true := by quickRfl

theorem kOuter25890 : CFSG.KC.TC2Outer.outerCheck0 256 innJ3K mulJ3K 1 = true := by quickRfl

theorem kEL25890 : decide (TableX.eListX 256 innJ3K mulJ3K 1 = EL25890) = true := by quickRfl

theorem kLab25890 : lab25890 = true := by quickRfl

theorem kWord25890 : (List.range 8).all (fun j => wordEqK 6156 13 (mask 13) (pidn 6156 13)
    PJ3.S PJ3.SI 5 (WD25890.getD j []) (wdVal j)) = true := by quickRfl

end CertificateChecks.KernelSpor.J3OutX25890

end
