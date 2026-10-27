module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2268

meta def baseH : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755 CFSG.Sporadic.Schreier.Tits.titsHBase

end CertificateChecks.KernelSpor.Tits2268

#ks_rawchain_sl2 CertificateChecks.KernelSpor.TitsH 1755 11 8 64 0
  CFSG.Sporadic.Schreier.Tits.titsHArrs CertificateChecks.KernelSpor.Tits2268.baseH 3
  CFSG.Sporadic.Schreier.Tits.titsHDerivations

namespace CertificateChecks.KernelSpor.Tits2268

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelMisc

theorem sOKH : allN 9 (fun j => Nat.beq (TitsH.S j) (TitsText.F (Nat.add 43 j))) = true := by
  quickRfl
theorem baseOKH : allN 5 (fun t => Nat.beq (baseArr 1755 titsHBase)[t]! (pg 11 (mask 11) TitsH.BP t)) =
    true := by quickRfl
theorem permH : allN 9 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsH.S j) (TitsH.SI j)) =
    true := by quickRfl

theorem bindsH : Binds 1755 11 TitsH.S 9 5 TitsH.BP titsHArrs (baseArr 1755 titsHBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsHArrs, titsField1755],
    fun j hj => by
      have e : TitsH.S j = TitsText.F (43 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKH j hj)
      rw [titsHArrs, CertificateChecks.KernelSpor.Tits2264.field_get hj (by norm_num), e],
    by decide, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKH t ht)⟩

end CertificateChecks.KernelSpor.Tits2268

end
