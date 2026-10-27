module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2268

meta def baseJ : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755 CFSG.Sporadic.Schreier.Tits.titsJBase

end CertificateChecks.KernelSpor.Tits2268

#ks_rawchain_sl2 CertificateChecks.KernelSpor.TitsJ 1755 11 8 64 0
  CFSG.Sporadic.Schreier.Tits.titsJArrs CertificateChecks.KernelSpor.Tits2268.baseJ 4
  CFSG.Sporadic.Schreier.Tits.titsJDerivations

namespace CertificateChecks.KernelSpor.Tits2268

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelMisc

theorem sOKJ : allN 9 (fun j => Nat.beq (TitsJ.S j) (TitsText.F (Nat.add 71 j))) = true := by
  quickRfl
theorem baseOKJ : allN 4 (fun t => Nat.beq (baseArr 1755 titsJBase)[t]! (pg 11 (mask 11) TitsJ.BP t)) =
    true := by quickRfl
theorem permJ : allN 9 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsJ.S j) (TitsJ.SI j)) =
    true := by quickRfl

theorem bindsJ : Binds 1755 11 TitsJ.S 9 4 TitsJ.BP titsJArrs (baseArr 1755 titsJBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsJArrs, titsField1755],
    fun j hj => by
      have e : TitsJ.S j = TitsText.F (71 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKJ j hj)
      rw [titsJArrs, CertificateChecks.KernelSpor.Tits2264.field_get hj (by norm_num), e],
    by decide, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKJ t ht)⟩

end CertificateChecks.KernelSpor.Tits2268

end
