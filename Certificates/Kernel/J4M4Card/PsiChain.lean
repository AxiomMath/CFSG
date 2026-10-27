module

public import Certificates.Data.Kernel.J4M4Card.PsiDefs
public import CFSG.Certificates.Kernel.Spor.RawDefs
public meta import Certificates.Data.Kernel.J4M4Card.PsiDefs
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4Card

open CFSG.KC.Enum CFSG.KS CFSG.KD.J4M4Card CFSG.Quasithin.J4M4Card

meta def psiS2 : Array (Array Nat) := psiS ()

meta def psiB2 : Array Nat := psiBase.toArray

meta def psiOL : Array Nat := Array.ofFn (n := 128) fun k => (psiOP >>> (12 * k.val)) &&& 4095

meta def psiR (i : Nat) : Array Nat :=
  let ms := maskTab.getD i []
  Array.ofFn (n := 128) fun k => ((psiOL.findIdx? (· == xorMasks ms psiOL[k.val]!)).getD 0)

meta def psiO17 : Array (Array Nat) :=
  (((List.range 62).filter fun i => (psiMP >>> (8 * i)) &&& 255 < 16).toArray.map psiR).push
    (Array.range 128)

meta def psiS128 : Array (Array Nat) :=
  (CFSG.YGroups.ModelNative.strongOf 128 psiO17 psiD128.toArray).1

meta def psiB128 : Array Nat := #[0, 1, 2]

end CertificateChecks.KernelJ4M4Card

#ks_rawchain CertificateChecks.KernelJ4M4Card.P2 2048 12 0 CertificateChecks.KernelJ4M4Card.psiS2
  CertificateChecks.KernelJ4M4Card.psiB2 62 CFSG.KD.J4M4Card.psiD

#ks_rawchain CertificateChecks.KernelJ4M4Card.P1 128 8 128 CertificateChecks.KernelJ4M4Card.psiS128
  CertificateChecks.KernelJ4M4Card.psiB128 17 CFSG.KD.J4M4Card.psiD128

namespace CertificateChecks.KernelJ4M4Card

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KD.J4M4Card CFSG.Quasithin.J4M4Card

theorem lane_ok : laneK P2.S 0 62 = true := by decide +kernel

theorem pair_ok : pairK P2.S P1.S = true := by decide +kernel

theorem rx_ok : rxK = true := by decide +kernel

theorem ov_ok : ovK = true := by decide +kernel

theorem span_ok : spanK = true := by decide +kernel

theorem orb2_ok : (List.range 4).map (fun i => rcnt (P2.LR i)) = [120, 84, 16, 2] := by
  decide +kernel

theorem orb1_ok : ((List.range 3).map fun i => rcnt (P1.LR i)).prod = 322560 := by
  decide +kernel

theorem neg_lane : laneK (fun i => P2.S (i + 3)) 0 1 = false := by decide +kernel

theorem neg_pair : pairK P2.S (fun j => P1.S (j + 1)) = false := by decide +kernel

end CertificateChecks.KernelJ4M4Card

end
