module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.LocalComp.HeRData
public import Certificates.Kernel.LocalComp.HeRSLPData
public import Certificates.Kernel.CosetJ.HeImgStr
public import Certificates.Data.Kernel.PermSLP
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Lie.CT.Core
import all Certificates.Data.HePresData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PermSLP
open CertificateChecks.KernelLC.HeFix CFSG.ComponentClassification.AS81.HePres.Native

open CertificateChecks.KernelCosetJ.HeImgStr in
@[expose] noncomputable def gw : List (List Int) :=
  List.map (fun cs => cs.map fun c : Char =>
      if c = 'a' then (1 : Int) else if c = 'A' then -1 else if c = 'b' then 2 else -2)
    [W0, W1, W2, W3, W4, W5, W6, W7]

open CertificateChecks.KernelCosetJ.HeImgStr in
theorem gw_eq : hePiHeWords = gw := by
  unfold hePiHeWords seedLetters
  simp only [List.map_cons, List.map_nil]
  rw [w0_toList, w1_toList, w2_toList, w3_toList, w4_toList, w5_toList, w6_toList, w7_toList]
  rfl

@[expose] noncomputable def WR (i : Nat) : List Int := gw.getD i []

@[expose] noncomputable def HRW (i : Nat) : Nat := symV 4 L2 L2I HSV (HST i)

@[expose] noncomputable def ltR (s : Nat) : Bool := letK 8330 14 4 L2 L2I HSV s

@[expose] noncomputable def ruR (k : Nat) : Bool := ruleK 8330 14 4 L2 L2I HSV HSG k

@[expose] noncomputable def toR (i : Nat) : Bool :=
  bAnd(topK 4 181 185 HSG (HST i) (WR i), bAnd(szOK 8330 14, lettersK 2 (WR i)))

theorem kCn : (cn (L2 0) && cn (L2 1) && cn (L2I 0) && cn (L2I 1) && cn 0) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeR

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.HeR.ltR 0 4
#kon_join CertificateChecks.KernelLC.HeR.ltAll CertificateChecks.KernelLC.HeR.ltR 4
#kon_slices CertificateChecks.KernelLC.HeR.ruR 0 181
#kon_join CertificateChecks.KernelLC.HeR.ruAll CertificateChecks.KernelLC.HeR.ruR 181
#kon_slices CertificateChecks.KernelLC.HeR.toR 0 8
#kon_join CertificateChecks.KernelLC.HeR.toAll CertificateChecks.KernelLC.HeR.toR 8

namespace CertificateChecks.KernelLC.HeR

open CFSG.KC.PermSLP CertificateChecks.KernelLC.HeFix
open CFSG.KLie.CT (notB)

theorem ruN_val : notB (ruleK 8330 14 4 L2 L2I (fun k => HSV (Nat.succ k)) HSG 0) = true := by
  quickRfl
theorem ruN_fwd : notB (ruleK 8330 14 4 L2 L2I HSV (fun _ => 262144) 0) = true := by quickRfl
theorem toN_word : notB (topK 4 181 185 HSG (HST 6) (WR 7)) = true := by quickRfl
theorem toN_sym : notB (topK 4 181 185 HSG 185 (WR 0)) = true := by quickRfl

end CertificateChecks.KernelLC.HeR

end
