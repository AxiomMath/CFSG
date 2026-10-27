module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2268

meta def baseN : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755 CFSG.Sporadic.Schreier.Tits.titsNBase

end CertificateChecks.KernelSpor.Tits2268

#ks_rawchain_sl2 CertificateChecks.KernelSpor.TitsN 1755 11 8 64 0
  CFSG.Sporadic.Schreier.Tits.titsNArrs CertificateChecks.KernelSpor.Tits2268.baseN 4
  CFSG.Sporadic.Schreier.Tits.titsNDerivations

namespace CertificateChecks.KernelSpor.Tits2268

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelMisc

theorem sOKN : allN 10 (fun j => Nat.beq (TitsN.S j) (TitsText.F (Nat.add 61 j))) = true := by
  quickRfl
theorem baseOKN : allN 5 (fun t => Nat.beq (baseArr 1755 titsNBase)[t]! (pg 11 (mask 11) TitsN.BP t)) =
    true := by quickRfl
theorem permN : allN 10 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsN.S j) (TitsN.SI j)) =
    true := by quickRfl

theorem bindsN : Binds 1755 11 TitsN.S 10 5 TitsN.BP titsNArrs (baseArr 1755 titsNBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsNArrs, titsField1755],
    fun j hj => by
      have e : TitsN.S j = TitsText.F (61 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKN j hj)
      rw [titsNArrs, CertificateChecks.KernelSpor.Tits2264.field_get hj (by norm_num), e],
    by decide, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKN t ht)⟩

end CertificateChecks.KernelSpor.Tits2268

end
