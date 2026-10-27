
module

public import Certificates.Kernel.GammaU.Orb16963OK
public import CFSG.Certificates.Kernel.GammaUOrbSound

public section

namespace CFSG.KD.GUO

open CFSG.KC.GUO CFSG.GF2Type.Smith1979.GammaU.StepA

theorem stepAOrbitFacts : StepAOrbitFacts := by
  obtain ⟨hTH, hSG, -, hR, -, hrows, -⟩ := co16963_pin
  have hrecs : ∀ i < 6, ∃ rs, repOK SG R i rs = true := by
    intro i hi
    interval_cases i
    exacts [⟨N0, co16963_n0⟩, ⟨N1, co16963_n1⟩, ⟨N2, co16963_n2⟩, ⟨N3, co16963_n3⟩,
      ⟨N4, co16963_n4⟩, ⟨N5, co16963_n5⟩]
  have hreps : ∀ i < 6, repF R i = true := by
    intro i hi
    interval_cases i
    exacts [co16963_r0, co16963_r1, co16963_r2, co16963_r3, co16963_r4, co16963_r5]
  obtain ⟨h1, h2, h3, h4⟩ := orbFacts_of ⟨hTH, hSG, hR, hrows⟩ hrecs hreps co16963_tree co16963_sm
    co16963_gens
  exact ⟨h1, h2, h3, h4⟩

end CFSG.KD.GUO

end
