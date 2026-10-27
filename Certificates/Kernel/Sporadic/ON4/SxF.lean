module

public import Certificates.Kernel.Sporadic.ON4.Defs
public import Certificates.Kernel.Sporadic.ON.GenF
public import Certificates.Kernel.Sporadic.FLGen
public import CFSG.Certificates.Kernel.Spor.TabWords
meta import Certificates.Kernel.Sporadic.ON3.Data
meta import Certificates.Kernel.Sporadic.ON4.WordsData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4K

@[expose] noncomputable def rd (f : Nat → Nat) (i : Nat) : Nat := f i

end CertificateChecks.KernelSpor.ON4K

namespace CertificateChecks.KernelSpor.ON4IM

open CertificateChecks.KernelSpor.ON4K

@[expose] noncomputable def A : Nat → Nat := iM 0
@[expose] noncomputable def B : Nat → Nat := iM 1
@[expose] noncomputable def T2 : Nat → Nat := iM 2
@[expose] noncomputable def T3 : Nat → Nat := iM 3
@[expose] noncomputable def T4 : Nat → Nat := iM 4
@[expose] noncomputable def U0 : Nat → Nat := iMI 0
@[expose] noncomputable def U1 : Nat → Nat := iMI 1
@[expose] noncomputable def U2 : Nat → Nat := iMI 2
@[expose] noncomputable def U3 : Nat → Nat := iMI 3
@[expose] noncomputable def U4 : Nat → Nat := iMI 4

end CertificateChecks.KernelSpor.ON4IM

namespace CertificateChecks.KernelSpor.ON4IL

open CertificateChecks.KernelSpor.ON4K

@[expose] noncomputable def A : Nat → Nat := iL 0
@[expose] noncomputable def B : Nat → Nat := iL 1
@[expose] noncomputable def T2 : Nat → Nat := iL 2
@[expose] noncomputable def T3 : Nat → Nat := iL 3
@[expose] noncomputable def U0 : Nat → Nat := iLI 0
@[expose] noncomputable def U1 : Nat → Nat := iLI 1
@[expose] noncomputable def U2 : Nat → Nat := iLI 2
@[expose] noncomputable def U3 : Nat → Nat := iLI 3

end CertificateChecks.KernelSpor.ON4IL

namespace CertificateChecks.KernelSpor.ON4IMc

open CertificateChecks.KernelSpor.ON4K

@[expose] noncomputable def A : Nat → Nat := iMc 0
@[expose] noncomputable def B : Nat → Nat := iMc 1
@[expose] noncomputable def T2 : Nat → Nat := iMc 2
@[expose] noncomputable def T3 : Nat → Nat := iMc 3
@[expose] noncomputable def T4 : Nat → Nat := iMc 4
@[expose] noncomputable def U0 : Nat → Nat := iMcI 0
@[expose] noncomputable def U1 : Nat → Nat := iMcI 1
@[expose] noncomputable def U2 : Nat → Nat := iMcI 2
@[expose] noncomputable def U3 : Nat → Nat := iMcI 3
@[expose] noncomputable def U4 : Nat → Nat := iMcI 4

end CertificateChecks.KernelSpor.ON4IMc

namespace CertificateChecks.KernelSpor.ON4ILc

open CertificateChecks.KernelSpor.ON4K

@[expose] noncomputable def A : Nat → Nat := iLc 0
@[expose] noncomputable def B : Nat → Nat := iLc 1
@[expose] noncomputable def T2 : Nat → Nat := iLc 2
@[expose] noncomputable def T3 : Nat → Nat := iLc 3
@[expose] noncomputable def T4 : Nat → Nat := iLc 4
@[expose] noncomputable def T5 : Nat → Nat := iLc 5
@[expose] noncomputable def U0 : Nat → Nat := iLcI 0
@[expose] noncomputable def U1 : Nat → Nat := iLcI 1
@[expose] noncomputable def U2 : Nat → Nat := iLcI 2
@[expose] noncomputable def U3 : Nat → Nat := iLcI 3
@[expose] noncomputable def U4 : Nat → Nat := iLcI 4
@[expose] noncomputable def U5 : Nat → Nat := iLcI 5

end CertificateChecks.KernelSpor.ON4ILc

#kon_nests CertificateChecks.KernelSpor.ON4K.rd CertificateChecks.KernelSpor.ON4IM
  CertificateChecks.KernelSpor.ON4N.M CertificateChecks.KernelSpor.ON3.wordsM 19 21
#kon_nests CertificateChecks.KernelSpor.ON4K.rd CertificateChecks.KernelSpor.ON4IL
  CertificateChecks.KernelSpor.ON4N.L CertificateChecks.KernelSpor.ON3.wordsM 21 23
#kon_nests CertificateChecks.KernelSpor.ON4K.rd CertificateChecks.KernelSpor.ON4IMc
  CertificateChecks.KernelSpor.ON4N.C CertificateChecks.KernelSpor.ON4.wordsM 0 2
#kon_nests CertificateChecks.KernelSpor.ON4K.rd CertificateChecks.KernelSpor.ON4ILc
  CertificateChecks.KernelSpor.ON4N.D CertificateChecks.KernelSpor.ON4.wordsM 2 5
#kon_nests CFSG.KS.ON.tab CertificateChecks.KernelSpor.ONV CertificateChecks.KernelSpor.ON4N.W
  CertificateChecks.KernelSpor.ON3.wordsM 30 34

namespace CertificateChecks.KernelSpor.ON4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW
open CertificateChecks.KernelSpor.ON3 (ZT M2T M3T L1T L2T trW mG mGI lG lGI)

theorem dM3 (i : Nat) : dM 3 i = ON4N.M19 i := by
  unfold dM
  rw [trace_eq]
  kernelRfl

theorem dM4 (i : Nat) : dM 4 i = ON4N.M20 i := by
  unfold dM
  rw [trace_eq]
  kernelRfl

theorem dL2 (i : Nat) : dL 2 i = ON4N.L21 i := by
  unfold dL
  rw [trace_eq]
  kernelRfl

theorem dL3 (i : Nat) : dL 3 i = ON4N.L22 i := by
  unfold dL
  rw [trace_eq]
  kernelRfl

theorem dMc3 (i : Nat) : dMc 3 i = ON4N.C0 i := by
  unfold dMc
  rw [trace_eq]
  kernelRfl

theorem dMc4 (i : Nat) : dMc 4 i = ON4N.C1 i := by
  unfold dMc
  rw [trace_eq]
  kernelRfl

theorem dLc3 (i : Nat) : dLc 3 i = ON4N.D2 i := by
  unfold dLc
  rw [trace_eq]
  kernelRfl

theorem dLc4 (i : Nat) : dLc 4 i = ON4N.D3 i := by
  unfold dLc
  rw [trace_eq]
  kernelRfl

theorem dLc5 (i : Nat) : dLc 5 i = ON4N.D4 i := by
  unfold dLc
  rw [trace_eq]
  kernelRfl

theorem trW_W30 (x : Nat) : trW 30 x = ON4N.W30 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_W31 (x : Nat) : trW 31 x = ON4N.W31 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_W32 (x : Nat) : trW 32 x = ON4N.W32 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_W33 (x : Nat) : trW 33 x = ON4N.W33 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

@[expose] noncomputable def dMF (j i : Nat) : Nat :=
  nIf(Nat.beq j 3, ON4N.M19 i, nIf(Nat.beq j 4, ON4N.M20 i, dM j i))
@[expose] noncomputable def dLF (j i : Nat) : Nat :=
  nIf(Nat.beq j 2, ON4N.L21 i, nIf(Nat.beq j 3, ON4N.L22 i, dL j i))
@[expose] noncomputable def dMcF (j i : Nat) : Nat :=
  nIf(Nat.beq j 3, ON4N.C0 i, nIf(Nat.beq j 4, ON4N.C1 i, dMc j i))
@[expose] noncomputable def dLcF (j i : Nat) : Nat :=
  nIf(Nat.beq j 3, ON4N.D2 i, nIf(Nat.beq j 4, ON4N.D3 i, nIf(Nat.beq j 5, ON4N.D4 i, dLc j i)))

@[expose] noncomputable def mGIF (h x : Nat) : Nat :=
  nIf(Nat.beq h 0, ZT x, nIf(Nat.beq h 1, ON4N.W30 x, ON4N.W31 x))
@[expose] noncomputable def lGIF (h x : Nat) : Nat := nIf(Nat.beq h 0, ON4N.W32 x, ON4N.W33 x)
@[expose] noncomputable def mcXF (y : Nat) : Nat := M3T (M2T (mGIF 2 (mGIF 1 y)))
@[expose] noncomputable def mcOF (j y : Nat) : Nat :=
  nIf(Nat.beq j 0, mcXF y, nIf(Nat.beq j 1, M2T (mcXF (mGIF 1 y)), M3T (mcXF (mGIF 2 y))))
@[expose] noncomputable def lcXF (y : Nat) : Nat := L2T (L1T (lGIF 1 (lGIF 0 y)))
@[expose] noncomputable def lcOF (j y : Nat) : Nat :=
  nIf(Nat.beq j 0, lcXF y, nIf(Nat.beq j 1, L1T (lcXF (lGIF 0 y)), L2T (lcXF (lGIF 1 y))))

@[expose] noncomputable def xMAtF (i : Nat) : Bool :=
  bAnd(xAt 27120 5 3 xM pM iM iMI mG dMF i, bAnd(xAt 27120 4 2 xM pM iL iLI lG dLF i,
    bAnd(xAt 27120 5 3 xM pM iMc iMcI mcOF dMcF i, xAt 27120 6 3 xM pM iLc iLcI lcOF dLcF i)))

@[expose] noncomputable def xMSF (s : Nat) : Bool :=
  allN (nat_lit 565) fun d => xMAtF (Nat.add (Nat.mul s (nat_lit 565)) d)

theorem dMF_eq : dMF = dM := by
  funext j i
  unfold dMF
  cases h3 : Nat.beq j 3
  · cases h4 : Nat.beq j 4
    · rfl
    · obtain rfl := Nat.eq_of_beq_eq_true h4
      exact (dM4 i).symm
  · obtain rfl := Nat.eq_of_beq_eq_true h3
    exact (dM3 i).symm

theorem dLF_eq : dLF = dL := by
  funext j i
  unfold dLF
  cases h2 : Nat.beq j 2
  · cases h3 : Nat.beq j 3
    · rfl
    · obtain rfl := Nat.eq_of_beq_eq_true h3
      exact (dL3 i).symm
  · obtain rfl := Nat.eq_of_beq_eq_true h2
    exact (dL2 i).symm

theorem dMcF_eq : dMcF = dMc := by
  funext j i
  unfold dMcF
  cases h3 : Nat.beq j 3
  · cases h4 : Nat.beq j 4
    · rfl
    · obtain rfl := Nat.eq_of_beq_eq_true h4
      exact (dMc4 i).symm
  · obtain rfl := Nat.eq_of_beq_eq_true h3
    exact (dMc3 i).symm

theorem dLcF_eq : dLcF = dLc := by
  funext j i
  unfold dLcF
  cases h3 : Nat.beq j 3
  · cases h4 : Nat.beq j 4
    · cases h5 : Nat.beq j 5
      · rfl
      · obtain rfl := Nat.eq_of_beq_eq_true h5
        exact (dLc5 i).symm
    · obtain rfl := Nat.eq_of_beq_eq_true h4
      exact (dLc4 i).symm
  · obtain rfl := Nat.eq_of_beq_eq_true h3
    exact (dLc3 i).symm

theorem mGIF_eq : mGIF = mGI := by
  funext h x
  unfold mGIF mGI
  rw [trW_W30, trW_W31]

theorem lGIF_eq : lGIF = lGI := by
  funext h x
  unfold lGIF lGI
  rw [trW_W32, trW_W33]

theorem mcOF_eq : mcOF = mcO := by
  funext j y
  unfold mcOF mcO mcXF mcX
  rw [mGIF_eq]

theorem lcOF_eq : lcOF = lcO := by
  funext j y
  unfold lcOF lcO lcXF lcX
  rw [lGIF_eq]

theorem xMS_of_F (s : Nat) (h : xMSF s = true) : xMS s = true := by
  unfold xMSF xMAtF at h
  rw [dMF_eq, dLF_eq, dMcF_eq, dLcF_eq, mcOF_eq, lcOF_eq] at h
  exact h

end CertificateChecks.KernelSpor.ON4K

end
