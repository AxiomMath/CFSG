
module

public import Certificates.Kernel.UnitarySix.Struct3010Base

public import Certificates.Kernel.UnitarySix.Letters
public import CFSG.Certificates.Kernel.U6Sound3010S
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

theorem struct3010 :
    (∀ x ∈ aGens, orderOf x = 2 ∧ ∀ y ∈ aGens, x * y = y * x) ∧
      (∀ k ∈ kGens ++ tGens, ∀ a ∈ aGens, k * a * k⁻¹ ∈ Subgroup.closure {g | g ∈ aGens}) ∧
      ∀ g ∈ tGens, g ∈ Subgroup.closure {g | g ∈ kGens} :=
  sound3010S letters_eq aWN_eq kWN_eq tWN_eq k3010S

open CFSG.Sporadic.Schreier in
theorem orbit3010 :
    (∀ a ∈ Subgroup.closure {g | g ∈ aGens}, a ≠ 1 →
        a ∈ conjClass (Subgroup.closure {g | g ∈ kGens}) j1 ∨
        a ∈ conjClass (Subgroup.closure {g | g ∈ kGens}) j2 ∨
        a ∈ conjClass (Subgroup.closure {g | g ∈ kGens}) j3) ∧
      (conjClass (Subgroup.closure {g | g ∈ kGens}) j1).ncard = 21 ∧
      (conjClass (Subgroup.closure {g | g ∈ kGens}) j2).ncard = 210 ∧
      (conjClass (Subgroup.closure {g | g ∈ kGens}) j3).ncard = 280 ∧
      orderOf j1 = 2 ∧ orderOf j2 = 2 ∧ orderOf j3 = 2 ∧
      {p : Fin 693 | j1 p = p}.ncard = 181 ∧ {p : Fin 693 | j2 p = p}.ncard = 53 ∧
      {p : Fin 693 | j3 p = p}.ncard = 21 :=
  sound3010O letters_eq aWN_eq kWN_eq tWN_eq k3010S k3010O

end CertificateChecks.KernelU6

end
