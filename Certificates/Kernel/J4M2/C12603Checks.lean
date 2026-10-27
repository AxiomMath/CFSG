module

public import Certificates.Data.Kernel.J4PrimeKerK
public import Certificates.Data.Kernel.SporSch.J4SBig
public import Certificates.Kernel.J4Q.MatData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4PrimeKernelData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4PrimeKernelData
public meta import Certificates.Kernel.SporSch.J4S.Gen
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec
public import Certificates.Kernel.SporSch.J4S.Gen

public section

set_option maxRecDepth 400000

#kss_rows CertificateChecks.KernelJ4PK.P5 CFSG.Sporadic.J4Schreier.kerP5
#kss_rows CertificateChecks.KernelJ4PK.I5 CFSG.Sporadic.J4Schreier.kerPinv5
#kss_rows CertificateChecks.KernelJ4PK.R5 CFSG.Sporadic.J4Schreier.kerR5
#kss_rows CertificateChecks.KernelJ4PK.P7 CFSG.Sporadic.J4Schreier.kerP7
#kss_rows CertificateChecks.KernelJ4PK.I7 CFSG.Sporadic.J4Schreier.kerPinv7
#kss_rows CertificateChecks.KernelJ4PK.R7 CFSG.Sporadic.J4Schreier.kerR7
#kss_rows CertificateChecks.KernelJ4PK.P23 CFSG.Sporadic.J4Schreier.kerP23
#kss_rows CertificateChecks.KernelJ4PK.I23 CFSG.Sporadic.J4Schreier.kerPinv23
#kss_rows CertificateChecks.KernelJ4PK.R23 CFSG.Sporadic.J4Schreier.kerR23
#kss_rows CertificateChecks.KernelJ4PK.P31 CFSG.Sporadic.J4Schreier.kerP31
#kss_rows CertificateChecks.KernelJ4PK.I31 CFSG.Sporadic.J4Schreier.kerPinv31
#kss_rows CertificateChecks.KernelJ4PK.R31 CFSG.Sporadic.J4Schreier.kerR31
#kss_rows CertificateChecks.KernelJ4PK.P37 CFSG.Sporadic.J4Schreier.kerP37
#kss_rows CertificateChecks.KernelJ4PK.I37 CFSG.Sporadic.J4Schreier.kerPinv37
#kss_rows CertificateChecks.KernelJ4PK.R37 CFSG.Sporadic.J4Schreier.kerR37

namespace CertificateChecks.KernelJ4PK

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4PK CFSG.Sporadic.J4Schreier

@[expose] noncomputable def chk (C : PrimeKerCase) (P Pi R : Nat) : Bool :=
  caseK c rm one A B Bi C.word C.exp C.order C.exps P Pi R C.k

theorem p5 : packNK kerP5.toList P5 = true := by quickRfl
theorem i5 : packNK kerPinv5.toList I5 = true := by quickRfl
theorem r5 : packNK kerR5.toList R5 = true := by quickRfl
theorem p7 : packNK kerP7.toList P7 = true := by quickRfl
theorem i7 : packNK kerPinv7.toList I7 = true := by quickRfl
theorem r7 : packNK kerR7.toList R7 = true := by quickRfl
theorem p23 : packNK kerP23.toList P23 = true := by quickRfl
theorem i23 : packNK kerPinv23.toList I23 = true := by quickRfl
theorem r23 : packNK kerR23.toList R23 = true := by quickRfl
theorem p31 : packNK kerP31.toList P31 = true := by quickRfl
theorem i31 : packNK kerPinv31.toList I31 = true := by quickRfl
theorem r31 : packNK kerR31.toList R31 = true := by quickRfl
theorem p37 : packNK kerP37.toList P37 = true := by quickRfl
theorem i37 : packNK kerPinv37.toList I37 = true := by quickRfl
theorem r37 : packNK kerR37.toList R37 = true := by quickRfl

theorem c5 : chk kerCase5 P5 I5 R5 = true := by quickRfl
theorem c7 : chk kerCase7 P7 I7 R7 = true := by quickRfl
theorem c23 : chk kerCase23 P23 I23 R23 = true := by quickRfl
theorem c29 : chk kerCase29 one one one = true := by quickRfl
theorem c31 : chk kerCase31 P31 I31 R31 = true := by quickRfl
theorem c37 : chk kerCase37 P37 I37 R37 = true := by quickRfl
theorem c43 : chk kerCase43 one one one = true := by quickRfl

theorem n5 : notB (chk { kerCase5 with order := 3 } P5 I5 R5) = true := by quickRfl
theorem n37 : notB (chk { kerCase37 with k := 107 } P37 I37 R37) = true := by quickRfl

end CertificateChecks.KernelJ4PK

end
