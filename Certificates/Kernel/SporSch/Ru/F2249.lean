
module

public import Certificates.Kernel.SporSch.Ru.CNFacts
public import Certificates.Kernel.SporSch.Ru.JFacts
public import Certificates.Kernel.SporSch.Ru.SmallFacts
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.RuCh

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem facts : (ruChainOK 4060 (ruField4060 1) 2 7 ruCBase ruCDerivations = true ∧
      rawOrbitSizes 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) = [1920, 64, 2] ∧
      (∀ i < 4, ruSift 4060 (ruField4060 1) ruCBase ruSGensA[i]! = true) ∧
      (∀ i < 8, ruSift 4060 (ruField4060 1) ruCBase ruKGensA[i]! = true))
    ∧ (ruChainOK 4060 (ruField4060 2) 2 6 ruNBase ruNDerivations = true ∧
      rawOrbitSizes 4060 (ruField4060 2) (ruBaseArr 4060 ruNBase) = [3584, 48, 2])
    ∧ (ruChainOK 4060 (ruField4060 3) 4 18 ruJoinBase ruJoinDerivations = true ∧
      rawOrbitSizes 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase) = [4060, 1755, 640, 32] ∧
      ruSift 4060 (ruField4060 3) ruJoinBase ruA0A = true ∧
      ruSift 4060 (ruField4060 3) ruJoinBase ruA1A = true)
    ∧ (ruChainOK 1920 (ruField1920 0) 2 7 ruCFaithfulBase ruCFaithfulDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase) = [1920, 128])
    ∧ (ruChainOK 80 ruField80 2 8 ruCQuotient80Base ruCQuotient80Derivations = true ∧
      rawOrbitSizes 80 ruField80 (ruBaseArr 80 ruCQuotient80Base) = [80, 64, 12, 2])
    ∧ (ruChainOK 1920 (ruField1920 1) 4 7 ruSBase ruSDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 1) (ruBaseArr 1920 ruSBase) = [1024, 16] ∧
      (∀ i < 6, ruSift 1920 (ruField1920 1) ruSBase (resA ruF ruFPos ruJGensA[i]!) = true) ∧
      (∀ i < 8, ruSift 1920 (ruField1920 1) ruSBase (resA ruF ruFPos ruKGensA[i]!) = true))
    ∧ (ruChainOK 1920 (ruField1920 2) 8 10 ruKBase ruKDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 2) (ruBaseArr 1920 ruKBase) = [512, 4] ∧
      ruSift 1920 (ruField1920 2) ruKBase (resA ruF ruFPos ruZA) = true)
    ∧ (ruChainOK 1920 (ruField1920 3) 6 10 ruJBase ruJDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 3) (ruBaseArr 1920 ruJBase) = [128, 16] ∧
      ruSift 1920 (ruField1920 3) ruJBase (resA ruF ruFPos ruZA) = true)
    ∧ (ruChainOK 1920 (ruField1920 4) 5 7 ruRBase ruRDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase) = [256, 8] ∧
      ruSift 1920 (ruField1920 4) ruRBase (resA ruF ruFPos ruZA) = true)
    ∧ (ruChainOK 6 ruCBlockStrong 2 6 [0, 2, 1] [[-2, -1], [-1, -1, 2, 1], [3, -4], [3, 4, 3]] =
        true ∧
      rawOrbitSizes 6 ruCBlockStrong (ruBaseArr 6 [0, 2, 1]) = [6, 5, 4] ∧
      ruChainOK 7 ruNBlockStrong 2 5 [1, 0, 2] [[-1, 2, 1], [-2, 3, 1], [3, -4, -3, 4, 3]] = true ∧
      rawOrbitSizes 7 ruNBlockStrong (ruBaseArr 7 [1, 0, 2]) = [7, 6, 4]) :=
  ⟨RuCNF.factsC, RuCNF.factsN, ⟨RuJ.chain, RuJ.orbits, RuJ.siftA0, RuJ.siftA1⟩, RuSF.facts⟩

end CertificateChecks.KernelSporSch.RuCh

end
