module

public import Certificates.Kernel.Sporadic.OddCore.SuzPairS
public import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzPair.w75343Sl 0 256
#kon_join CertificateChecks.KernelSpor.SuzPair.w75343All CertificateChecks.KernelSpor.SuzPair.w75343Sl 256

namespace CertificateChecks.KernelSpor.SuzPair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.LocalAnalysis.WeakClosure81.SporSuz
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzRF

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "T1" => SuzInvT1.F 0
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)

theorem kSelZ : selFrom (fun k => Nat.beq (wg SuzPairWZ k) 0) 8192 0 [0, 174] = true := by
  quickRfl

theorem kSel2 : selFrom (fun k => Nat.beq (wg SuzPairW2 k) 0) 8192 0 [0, 174, 8113, 8149] =
    true := by
  quickRfl

theorem kCan : allN 6 (fun i => cn (SuzPairT i)) = true := by quickRfl

theorem kInv : (ie Suz2306.B0 (SuzPairT 0) && ie Suz2306.B1 (SuzPairT 1) &&
    ie (SuzInvT1.F 20) (SuzPairT 2) && ie (SuzInvT1.F 22) (SuzPairT 3) &&
    ie (SuzPairT 4) (SuzPairT 5)) = true := by
  quickRfl

theorem kG : Nat.beq (SuzPairT 4) (iwK abK abIK gWord) = true := by quickRfl

theorem kInvW : (allN 2 (fun j => Nat.beq (pc (abIK j) (abK j)) Id) &&
    allN 3 (fun j => Nat.beq (pc (cgIK j) (cgK j)) Id)) = true := by
  quickRfl

theorem kGen : (Nat.beq (iwK cgK cgIK b0Word) Suz2306.B0 &&
    Nat.beq (iwK cgK cgIK b1Word) Suz2306.B1) = true := by
  quickRfl

theorem kE : (Nat.beq (SuzRFS.T 0) Id && Nat.beq (SuzRFS.T 174) T1) = true := by quickRfl

theorem kGN : (inVK (SuzPairT 4) T1 && inVK (SuzPairT 4) (SuzRFS.T 8113) &&
    !Nat.beq (pc (SuzPairT 4) T1) (pc T1 (SuzPairT 4))) = true := by
  quickRfl

theorem negZ : bAnd(Bool.not (zK (SuzRFS.T 1) 0), Bool.not (z2K (SuzRFS.T 174) 1)) = true := by
  quickRfl

theorem negSel : Bool.not (selFrom (fun k => Nat.beq (wg SuzPairWZ k) 0) 8192 0 [0]) = true := by
  quickRfl

theorem negG : bAnd(Bool.not (Nat.beq (SuzPairT 4) (iwK abK abIK gWord.tail)),
    Bool.not (ie Suz2306.B0 (Nat.xor (SuzPairT 0) 2))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.SuzPair

end
