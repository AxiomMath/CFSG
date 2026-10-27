module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2268

meta def baseR : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755 CFSG.Sporadic.Schreier.Tits.titsRBase

end CertificateChecks.KernelSpor.Tits2268

#ks_rawchain_sl2 CertificateChecks.KernelSpor.TitsR 1755 11 8 64 0
  CFSG.Sporadic.Schreier.Tits.titsRArrs CertificateChecks.KernelSpor.Tits2268.baseR 3
  CFSG.Sporadic.Schreier.Tits.titsRDerivations

namespace CertificateChecks.KernelSpor.Tits2268

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelMisc

theorem sOKR : allN 8 (fun j => Nat.beq (TitsR.S j) (TitsText.F (Nat.add 87 j))) = true := by
  quickRfl
theorem baseOKR : allN 5 (fun t => Nat.beq (baseArr 1755 titsRBase)[t]! (pg 11 (mask 11) TitsR.BP t)) =
    true := by quickRfl
theorem permR : allN 8 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsR.S j) (TitsR.SI j)) =
    true := by quickRfl

theorem bindsR : Binds 1755 11 TitsR.S 8 5 TitsR.BP titsRArrs (baseArr 1755 titsRBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsRArrs, titsField1755],
    fun j hj => by
      have e : TitsR.S j = TitsText.F (87 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKR j hj)
      rw [titsRArrs, CertificateChecks.KernelSpor.Tits2264.field_get hj (by norm_num), e],
    by decide, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKR t ht)⟩

end CertificateChecks.KernelSpor.Tits2268

end
