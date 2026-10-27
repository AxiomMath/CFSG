module

public import Certificates.Kernel.Sporadic.Fi22.X2069PL0
public import Certificates.Kernel.Sporadic.Fi22.X2069PL1
public import Certificates.Kernel.Sporadic.Fi22.X2069PL2
public import Certificates.Kernel.Sporadic.Fi22.X2069PL3
public import Certificates.Kernel.Sporadic.Fi22.X2069PL4
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.Monster.B.Fischer.PinnedChainInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

set_option Elab.async false in
#ks_rawchain_sl2_join CertificateChecks.KernelSpor.Fi22PC

namespace CertificateChecks.KernelSpor.Fi22X

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Fischer

theorem sOKP : allN 19 (fun j => Nat.beq (Fi22PC.S j) (Fi22ChT.F j)) = true := by quickRfl
theorem baseOKP : allN 6 (fun t => Nat.beq fi22BaseArr[t]! (pg 12 (mask 12) Fi22PC.BP t)) = true := by
  quickRfl
theorem permP : allN 19 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (Fi22PC.S j) (Fi22PC.SI j)) =
    true := by quickRfl

theorem bindsP : Binds 3510 12 Fi22PC.S 19 6 Fi22PC.BP fi22StrongArrs fi22BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22StrongArrs], fun j hj => ?_,
    by simp [fi22BaseArr, fi22ChainBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKP t ht)⟩
  rw [strong_eq hj, Nat.eq_of_beq_eq_true (allN_spec sOKP j hj)]

end CertificateChecks.KernelSpor.Fi22X

end
