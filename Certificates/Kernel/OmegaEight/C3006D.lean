module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverData
public import Certificates.Data.Kernel.CycTabW
public meta import Certificates.Kernel.OmegaEight.C3006Gen
import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

#kc_eval CertificateChecks.KernelO8.C3006 D CertificateChecks.KernelO8.C3006.step3006

namespace CertificateChecks.KernelO8.C3006

open CFSG.EvenSmallLie.OmegaEight.Cover CFSG.KC.CycTabW

@[expose] def csX : List (List (List ℕ)) := (List.finRange 8).map genCycles

@[expose] def csR : List (List (List ℕ)) := (List.finRange 4).map rhoCycles

@[expose] def zL (z : ℤ) : Fin 8 × Bool := (Fin.ofNat 8 (z.natAbs - 1), decide (0 < z))

@[expose] def gcX : List (List ℕ) := (List.finRange 4).map fun i => ((genCodes i).map zL).map codeW

end CertificateChecks.KernelO8.C3006

end
