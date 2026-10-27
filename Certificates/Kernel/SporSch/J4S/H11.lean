
module

public import Certificates.Kernel.SporSch.J4S.Three
public import Certificates.Data.Kernel.SporSch.J4SPow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentralizerH11Data
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentralizerH11Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.J4SCommGenBase
public import CFSG.Sporadic.Schreier.J4SPrimes
meta import CFSG.Sporadic.Schreier.J4SCommGenBase
meta import CFSG.Sporadic.Schreier.J4SPrimes
meta import CFSG.Sporadic.Schreier.J4SThreeDataInputs

public section

set_option maxRecDepth 400000

#kss_array CertificateChecks.KernelSporSch.J4HB CFSG.Sporadic.J4Schreier.h11B 11 11
#kss_array CertificateChecks.KernelSporSch.J4HBI CFSG.Sporadic.J4Schreier.h11Binv 11 11

namespace CertificateChecks.KernelSporSch.J4H11

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4XY

@[expose] noncomputable def polyA (A w : Nat) : Nat := packK fun i => appK (powKF 4 A i) w

@[expose] noncomputable def polyK (w : Nat) : Nat := polyA (W a276Word) w

@[expose] noncomputable def xK (w : Nat) : Nat := compK (polyK w) J4HBI

@[expose] noncomputable def p1024K (w : Nat) : Bool :=
  strictB (xK w) fun X => Nat.beq (powKF 11 X 1024) X

@[expose] noncomputable def ord3K (w : Nat) : Bool :=
  strictB (xK w) fun X => strictB (powKF 2 X 3) fun Y =>
    bIf(Nat.beq Y pidK, bIf(Nat.beq X pidK, true, Nat.blt (fixCntK X) 4),
      bAnd(canonK Y, bAnd(canonK pidK, Bool.not (Nat.beq Y pidK))))

theorem b1 : Nat.beq (polyK 1) J4HB = true := by quickRfl

theorem binv : Nat.beq (compK J4HB J4HBI) pidK = true := by quickRfl

theorem p1024 : allN 2048 p1024K = true := by quickRfl

theorem ord3 : allN 2048 ord3K = true := by quickRfl

theorem q3fix : allN 27 (fun k => bIf(Nat.beq k 0, true, Nat.ble 4 (fixCntK (J4Q3C k)))) = true := by
  quickRfl

theorem neg_b1 : Bool.not (Nat.beq (polyK 2) J4HB) = true := by quickRfl

theorem neg_binv : Bool.not (Nat.beq (compK J4HB J4HB) pidK) = true := by quickRfl

theorem neg_p512 : Bool.not (allN 2048 fun w => strictB (xK w) fun X => Nat.beq (powKF 11 X 512) X) =
    true := by quickRfl

theorem neg_ord3 : Bool.not (allN 2048 fun w => strictB (xK w) fun X =>
    bIf(Nat.beq (powKF 2 X 3) pidK, bIf(Nat.beq X pidK, true, Nat.blt (fixCntK X) 2), true)) =
    true := by quickRfl

theorem neg_q3fix : Bool.not (allN 27 (fun k => bIf(Nat.beq k 0, true, Nat.ble 9 (fixCntK (J4Q3C k))))) =
    true := by quickRfl

end CertificateChecks.KernelSporSch.J4H11

end
