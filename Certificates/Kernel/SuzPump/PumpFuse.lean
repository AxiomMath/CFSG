module

public import Certificates.Kernel.SuzPump.PumpSrc
public import Certificates.Kernel.SuzPump.Pair
public import Certificates.Kernel.SuzPump.PumpY
public import Certificates.Kernel.Sporadic.OddCore.S8147D
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.Text
meta import Certificates.Kernel.SuzPump.PumpSrc
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSuzPump.FT CFSG.HardMathSupport.Solomon.Coordinator.SuzPump.fuseText
#kmisc_packarrs CertificateChecks.KernelSuzPump.FR CertificateChecks.KernelSuzPump.fuseRows 11
#kmisc_packarrs CertificateChecks.KernelSuzPump.FTS CertificateChecks.KernelSuzPump.fuseTs 11
#kmisc_packarrs CertificateChecks.KernelSuzPump.FNS CertificateChecks.KernelSuzPump.fuseNs 11

public section

namespace CertificateChecks.KernelSuzPump

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CFSG.KC.LQT.P (anyN)

theorem fbind : CFSG.KS.Text.hexBind (FT.chars ++ ['\n']) 3 14 11 300 0 300 FR = true := by
  quickRfl

@[expose] noncomputable def siftOK (X : Nat) : Bool :=
  Nat.beq (Nat.shiftRight X (1782 * 11)) 0 &&
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) X t) 1782) && permB 1782 11 X &&
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 X

@[expose] noncomputable def rowK (j : Nat) : Bool :=
  let R := FR j
  let tb := rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => pg 11 (mask 11) R (l + 1)) 6
  let nb := rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => pg 11 (mask 11) R (l + 7)) 6
  tb.2.2 && nb.2.2 && Nat.beq tb.1 (FTS j) && Nat.beq nb.1 (FNS j) && siftOK (FTS j) &&
    siftOK (FNS j) &&
    permOK 1782 11 (mask 11) (1782 * 11) (FNS j) (pinvS 1782 11 (mask 11) (FNS j)) &&
    Nat.beq (cm 1782 11 (FNS j) (cm 1782 11 (FTS j) (pinvS 1782 11 (mask 11) (FNS j))))
      (if Nat.beq (pg 11 (mask 11) R 13) 0 then XA else YY)

@[expose] noncomputable def rowsB (b : Nat) : Bool := allN 10 (fun r => rowK (10 * b + r))

theorem fxa : Nat.beq (pw 1782 11 XA 3) (pidn 1782 11) = true ∧
    (!Nat.beq XA (pidn 1782 11)) = true ∧ siftOK XA = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def elK (i P : Nat) : Bool :=
  !(Nat.beq (pw 1782 11 P 3) (pidn 1782 11)) || Nat.beq P (pidn 1782 11) ||
    (anyN 300 (fun j => Nat.beq (pg 11 (mask 11) (FR j) 0) i && Nat.beq P (FTS j)) &&
      (!Nat.beq i 0 || !Nat.beq (cm 1782 11 P (SFvT.F 1)) (cm 1782 11 (SFvT.F 1) P)))

@[expose] noncomputable def mv3 (P t : Nat) : Bool :=
  !Nat.beq (pg 11 (mask 11) P (pg 11 (mask 11) P (pg 11 (mask 11) P t))) t

@[expose] noncomputable def elQ (i P : Nat) : Bool :=
  mv3 P 0 || mv3 P 1 || mv3 P 2 || mv3 P 3 || elK i P

@[expose] noncomputable def elB (i : Nat) (T : Nat → Nat) (b : Nat) : Bool :=
  allN 600 (fun r => elQ i (T (600 * b + r)))

theorem fel1 : allN 600 (fun k => elK 1 (SFC1.T k)) = true := by quickRfl
theorem fel2 : allN 600 (fun k => elK 2 (SFC2.T k)) = true := by quickRfl
theorem fel5 : allN 600 (fun k => elK 5 (SFC5.T k)) = true := by quickRfl

theorem frow_neg : (!Nat.beq (cm 1782 11 (FNS 0) (cm 1782 11 (FTS 0)
    (pinvS 1782 11 (mask 11) (FNS 0)))) (FTS 0)) = true := by quickRfl

theorem fel_neg : (!elK 6 (FTS 0)) = true := by quickRfl

end CertificateChecks.KernelSuzPump

end
