module

public import Certificates.Kernel.Sporadic.OddCore.Suz26990
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma44SuzL34Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.EvenSporadicStandard.Solomon78 CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

@[expose] def l10741TA : Array Nat :=
  #[1, 2, 0, 3, 4, 14, 18, 6, 10, 17, 13, 9, 5, 8, 12, 16, 20, 11, 7, 19, 15, 36, 27, 38, 24, 33,
    26, 41, 23, 31, 21, 34, 37, 35, 29, 25, 30, 39, 28, 32, 40, 22]

@[expose] def l10741TB : Array Nat :=
  #[5, 10, 20, 2, 15, 7, 6, 0, 8, 4, 14, 12, 19, 17, 1, 9, 13, 16, 18, 11, 3, 37, 22, 33, 29, 41,
    23, 27, 40, 30, 24, 39, 32, 26, 25, 31, 28, 38, 21, 35, 36, 34]

@[expose] noncomputable def restrK (p : Nat) (T : Array Nat) : Bool :=
  (List.range 42).all fun i =>
    Nat.beq (pg 11 (mask 11) p suzL34Pts[i]!) suzL34Pts[T[i]!]!

@[expose] def l10741WordTab (w : List Nat) : Array Nat :=
  w.foldl (fun acc l => comp 42 acc (if l = 1 then l10741TA else l10741TB)) (idTab 42)

theorem k10741 : strictB PA (fun a => strictB PB fun b =>
    andB (restrK a l10741TA) (restrK b l10741TB)) = true := by
  quickRfl

theorem k10741P : (suzL34PtsOK && (List.range 42).all fun i =>
    decide (l10741TA[i]! < 42) && decide (l10741TB[i]! < 42)) = true := by
  decide +kernel

theorem k10741I : ((List.range 42).all fun j => suzL34Index suzL34Pts[j]! == j) = true := by
  decide +kernel

theorem k10741W : ((l10741WordTab suzL34G1 == g₁T) && (l10741WordTab suzL34G2 == g₂T) &&
    (l10741WordTab suzL34G3 == g₃T)) = true := by
  decide +kernel

end CertificateChecks.KernelSpor.S26990

end
