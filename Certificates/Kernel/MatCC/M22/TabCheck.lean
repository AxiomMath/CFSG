module

public import CFSG.Certificates.Kernel.Spor.RelSound
public import CFSG.Sporadic.Recognition.M22MultiplierInputs
import CFSG.Certificates.Kernel.Common.Harness
import Init.Data.Range.Basic
import Init.Data.Nat.Fold
import Init.Data.Array.Basic
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelM22Tab

open CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Recognition.M22Multiplier CFSG.KS.Rel
  CFSG.Sporadic.Recognition.CoverRecipe

theorem rels_K : relK 22 5 tabA tabA tabB tabBi (m22CheckWords.map natWord) = true := by
  quickRfl

theorem m22TabCheck_true : m22TabCheck = true := by
  unfold m22TabCheck
  exact relK_sound rels_K

end CertificateChecks.KernelM22Tab

end
