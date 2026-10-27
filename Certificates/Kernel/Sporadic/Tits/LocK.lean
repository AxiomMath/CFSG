module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2268

meta def baseK : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755 CFSG.Sporadic.Schreier.Tits.titsKBase

end CertificateChecks.KernelSpor.Tits2268

#ks_rawchain_sl2 CertificateChecks.KernelSpor.TitsK 1755 11 8 64 0
  CFSG.Sporadic.Schreier.Tits.titsKArrs CertificateChecks.KernelSpor.Tits2268.baseK 2
  CFSG.Sporadic.Schreier.Tits.titsKDerivations

namespace CertificateChecks.KernelSpor.Tits2268

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelMisc

theorem sOKK : allN 7 (fun j => Nat.beq (TitsK.S j) (TitsText.F (Nat.add 80 j))) = true := by
  quickRfl
theorem baseOKK : allN 5 (fun t => Nat.beq (baseArr 1755 titsKBase)[t]! (pg 11 (mask 11) TitsK.BP t)) =
    true := by quickRfl
theorem permK : allN 7 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsK.S j) (TitsK.SI j)) =
    true := by quickRfl

theorem bindsK : Binds 1755 11 TitsK.S 7 5 TitsK.BP titsKArrs (baseArr 1755 titsKBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsKArrs, titsField1755],
    fun j hj => by
      have e : TitsK.S j = TitsText.F (80 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKK j hj)
      rw [titsKArrs, CertificateChecks.KernelSpor.Tits2264.field_get hj (by norm_num), e],
    by decide, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKK t ht)⟩

end CertificateChecks.KernelSpor.Tits2268

end
