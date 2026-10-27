module

public import Certificates.Kernel.LocalComp.TW.M22
public import Certificates.Kernel.LocalComp.TW.M23
public import Certificates.Kernel.LocalComp.TW.M24a
public import Certificates.Kernel.LocalComp.TW.M24b
public import CFSG.Certificates.Kernel.LocalCompThreeWitnessSound
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
public meta import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.MathieuOddCore

public section

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier CFSG.KC.LocalComp.ThreeW

namespace CertificateChecks.KernelLC.TW

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd in
open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
open CFSG.Certificates in
theorem facts : (threeWitnessOK 23 (listTables m23KGens) (listInvTables m23KGens)
      (toTable (evalCodes m23KGens [3, 3, 3])) (toTable (evalCodes m23KGens [3, 3])) 1000 =
      true
    )
    ∧ (threeWitnessOK 24 (listTables m24K1Gens) (listInvTables m24K1Gens)
      (toTable (evalCodes m24K1Gens [2, 2])) (toTable (evalCodes m24K1Gens [2, 1, 2, 1])) 1000 =
      true
    )
    ∧ (threeWitnessOK 24 (listTables m24K2Gens) (listInvTables m24K2Gens)
      (toTable (evalCodes m24K2Gens [2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1]))
      (toTable (evalCodes m24K2Gens [2, 1, 1, 1, 2, 1, 1, 1])) 1000 = true
    )
    ∧ (threeWitnessOK 22 (listTables m22OKGens) (listInvTables m22OKGens)
      (toTable (evalCodes m22OKGens [1, 1])) (toTable (evalCodes m22OKGens [3, 1])) 1000 =
      true
    ) :=
  ⟨threeWitnessOK_of_K m23K,
    threeWitnessOK_of_K_eq m24a_gens m24a_invs m24a_q m24a_y m24aK,
    threeWitnessOK_of_K_eq m24b_gens m24b_invs m24b_q m24b_y m24bK,
    threeWitnessOK_of_K m22K⟩

end CertificateChecks.KernelLC.TW
