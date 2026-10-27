
module

public import Certificates.Kernel.HN3166.SimpleBase

public import Certificates.Kernel.HN3166.Card
public import Certificates.Kernel.HN3166.Alg
public import CFSG.Sporadic.HN.CoprimeSimple

public section

namespace CertificateChecks.KernelHN

open CFSG.Sporadic.F5 CFSG.Sporadic.HN

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

theorem facts3166 :
    mA Dt ^ 2 = 1 ∧ mB Dt ^ 3 = 1 ∧ (∃ g : J Dt, orderOf (a Dt * (g⁻¹ * b Dt * g)) = 19) ∧
      (∀ M : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5), M * mA Dt = mA Dt * M →
        M * mB Dt = mB Dt * M → ∃ c : ZMod 5, M = c • 1) ∧
      Nat.card (J Dt) = 273030912000000 :=
  ⟨mA_sq, mB_cube, orderOf_x, commutant_scalar, card_J⟩

theorem isSimpleGroup_J :
    IsSimpleGroup (J Dt) := by
  obtain ⟨g, hg⟩ := orderOf_x
  exact simple_of_facts a_sq b_cube hg center_J card_J

end CertificateChecks.KernelHN

end
