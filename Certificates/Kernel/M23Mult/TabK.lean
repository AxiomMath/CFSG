module

public import Certificates.Data.Kernel.Spor.Rel
public import CFSG.Sporadic.Recognition.M23MultiplierInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Schreier.M23

public section

namespace CertificateChecks.KernelM23Mult

open CFSG.Sporadic.Bridge.M23 CFSG.Sporadic.Recognition.M23Multiplier CFSG.KS.Rel
  CFSG.Sporadic.Recognition.CoverRecipe

theorem tabK : relK 23 5 tabA tabA tabBi tabB (m23CheckWords.map natWord) = true := by
  quickRfl

end CertificateChecks.KernelM23Mult

end
