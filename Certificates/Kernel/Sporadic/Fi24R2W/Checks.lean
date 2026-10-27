module

public import Certificates.Kernel.Sporadic.Fi24R2W.Data
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Kernel.Sporadic.Fi24K.K2077
public import Certificates.Data.Kernel.Spor.Fi24R2W
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelSpor.Fi24R2W

open CFSG.KC.Fi24R2W CFSG.KD.Fi24Net CFSG.KC.Enum

theorem st0_t : stageOK NW H0 S0 = true := by quickRfl

theorem st1_t : stageOK NW H1 S1 = true := by quickRfl

theorem st2_t : stageOK NW (hwS S0 S1 dWL) SD1 = true := by quickRfl

theorem st3_t : stageOK NW (List.replicate 7 SD1).flatten SD = true := by quickRfl

theorem st4_t : stageOK NW (SD ++ (S0 ++ (SD ++ invC S0))) SU2 = true := by quickRfl

theorem st5_t : stageOK NW (hwS S0 S1 wWL) SW = true := by quickRfl

theorem st6_t : stageOK NW (SU2 ++ (SW ++ (SD ++ invC SW))) SR = true := by quickRfl

theorem cmA_t : stageOK NW (SA ++ SR) (SR ++ SA) = true := by quickRfl

theorem cmB_t : stageOK NW (SB ++ SR) (SR ++ SB) = true := by quickRfl

theorem fix_t : plOK NW SR FP.F (fun i => i) = true := by quickRfl


theorem kr0_t : allN 504 (fun j => Nat.blt (krow (Fi24KC.S 0) j) 504) = true := by quickRfl

theorem kr1_t : allN 504 (fun j => Nat.blt (krow (Fi24KC.S 1) j) 504) = true := by quickRfl

theorem mono_t : allN 503 (fun j => Nat.blt (fpt FP.F j) (fpt FP.F (Nat.succ j))) = true := by
  quickRfl

theorem top_t : Nat.blt (fpt FP.F 503) 306936 = true := by quickRfl

end CertificateChecks.KernelSpor.Fi24R2W

end
