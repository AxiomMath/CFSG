module

public import Certificates.Kernel.Fin76bAut.Data
public import Certificates.Data.Kernel.Fin76bAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFin76bAut

open CFSG.KS.EAut CFSG.EvenSporadicStandard.Fin76b.W16

theorem ch24614Tab : eTabK ET mulE0 = true := by quickRfl

end CertificateChecks.KernelFin76bAut

end
