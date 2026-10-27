module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2268

meta def baseS : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755 CFSG.Sporadic.Schreier.Tits.titsSBase

end CertificateChecks.KernelSpor.Tits2268

#ks_rawchain_sl2 CertificateChecks.KernelSpor.TitsS 1755 11 8 64 0
  CFSG.Sporadic.Schreier.Tits.titsSArrs CertificateChecks.KernelSpor.Tits2268.baseS 3
  CFSG.Sporadic.Schreier.Tits.titsSDerivations

namespace CertificateChecks.KernelSpor.Tits2268

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelMisc

theorem sOKS : allN 9 (fun j => Nat.beq (TitsS.S j) (TitsText.F (Nat.add 52 j))) = true := by
  quickRfl
theorem baseOKS : allN 5 (fun t => Nat.beq (baseArr 1755 titsSBase)[t]! (pg 11 (mask 11) TitsS.BP t)) =
    true := by quickRfl
theorem permS : allN 9 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsS.S j) (TitsS.SI j)) =
    true := by quickRfl

theorem bindsS : Binds 1755 11 TitsS.S 9 5 TitsS.BP titsSArrs (baseArr 1755 titsSBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsSArrs, titsField1755],
    fun j hj => by
      have e : TitsS.S j = TitsText.F (52 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKS j hj)
      rw [titsSArrs, CertificateChecks.KernelSpor.Tits2264.field_get hj (by norm_num), e],
    by decide, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKS t ht)⟩

end CertificateChecks.KernelSpor.Tits2268

end
