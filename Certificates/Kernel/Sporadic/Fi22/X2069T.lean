
module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.Fi22.X2069Ext
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22X

meta def baseTM : Array Nat := #[0, 1, 2, 3, 6, 4]

end CertificateChecks.KernelSpor.Fi22X

#ks_rawchain_sl2 CertificateChecks.KernelSpor.Fi22TC 3510 12 0 64 0
  CertificateChecks.KernelSpor.Fi22X.outT4M CertificateChecks.KernelSpor.Fi22X.baseTM 13
  CertificateChecks.KernelSpor.Fi22X.nilD

namespace CertificateChecks.KernelSpor.Fi22X

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Fischer

theorem sOKT : allN 13 (fun j => Nat.beq (Fi22TC.S j) (TS j)) = true := by quickRfl
theorem baseOKT : allN 6 (fun t => Nat.beq (#[0, 1, 2, 3, 6, 4] : Array Nat)[t]! (pg 12 (mask 12) Fi22TC.BP t)) =
    true := by quickRfl
theorem permT : allN 13 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (Fi22TC.S j) (Fi22TC.SI j)) =
    true := by quickRfl

theorem bindsT : Binds 3510 12 Fi22TC.S 13 6 Fi22TC.BP (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22OuterStrong3510, fi22OuterLines3510],
    fun j hj => ?_, by simp, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKT t ht)⟩
  rw [outT_eq hj, Nat.eq_of_beq_eq_true (allN_spec sOKT j hj)]

end CertificateChecks.KernelSpor.Fi22X

end
