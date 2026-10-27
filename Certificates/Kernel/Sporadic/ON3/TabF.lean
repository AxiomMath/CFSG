module

public import Certificates.Kernel.Sporadic.ON3.Defs
public import Certificates.Kernel.Sporadic.ON.GenF
public import Certificates.Kernel.Sporadic.FLGen
public import CFSG.Certificates.Kernel.Spor.TabWords
meta import Certificates.Kernel.Sporadic.ON3.Data

public section

set_option maxRecDepth 400000

#kon_nests CFSG.KS.ON.tab CertificateChecks.KernelSpor.ONV CertificateChecks.KernelSpor.ON3N.N
  CertificateChecks.KernelSpor.ON3.wordsM 0 11

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW

theorem trW_N0 (x : Nat) : trW 0 x = ON3N.N0 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N1 (x : Nat) : trW 1 x = ON3N.N1 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N2 (x : Nat) : trW 2 x = ON3N.N2 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N3 (x : Nat) : trW 3 x = ON3N.N3 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N4 (x : Nat) : trW 4 x = ON3N.N4 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N5 (x : Nat) : trW 5 x = ON3N.N5 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N6 (x : Nat) : trW 6 x = ON3N.N6 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N7 (x : Nat) : trW 7 x = ON3N.N7 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N8 (x : Nat) : trW 8 x = ON3N.N8 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N9 (x : Nat) : trW 9 x = ON3N.N9 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

theorem trW_N10 (x : Nat) : trW 10 x = ON3N.N10 x := by
  unfold trW
  rw [trace_eq]
  kernelRfl

@[expose] noncomputable def tabAtF (x : Nat) : Bool :=
  strictB (ZT x) fun z => strictB (QT x) fun q => strictB (CT x) fun c => strictB (CIT x) fun ci =>
  strictB (WT x) fun w =>
  bAnd(Nat.beq z (ON3N.N0 x), bAnd(Nat.beq q (ON3N.N1 x), bAnd(Nat.beq c (ON3N.N2 x),
  bAnd(Nat.beq (CIT c) x,
  bAnd(Nat.beq (D1T x) (ON3N.N3 x), bAnd(Nat.beq (D2T x) (ON3N.N4 x),
  bAnd(Nat.beq (D3T x) (ON3N.N5 x), bAnd(Nat.beq (D4T x) (ON3N.N6 x),
  bAnd(Nat.beq (M2T x) (ON3N.N7 x), bAnd(Nat.beq (M3T x) (ON3N.N8 x),
  bAnd(Nat.beq (L1T x) (ON3N.N9 x), bAnd(Nat.beq (L2T x) (ON3N.N10 x),
  bAnd(Nat.beq w (CT (QT (QT ci))),
  bAnd(Nat.beq (ZT z) x, bAnd(Nat.beq (M2T z) (ZT (M2T x)), bAnd(Nat.beq (M3T z) (ZT (M3T x)),
  bAnd(Nat.beq (QT (QT (QT q))) x, bAnd(Nat.beq (L1T q) (QT (L1T x)),
  bAnd(Nat.beq (L2T q) (QT (L2T x)), bAnd(Nat.beq (D1T x) (CT (ZT ci)),
  allN 4 fun j => Nat.beq (WT (DT j x)) (DT j w)))))))))))))))))))))

theorem tabAt_eq_F (x : Nat) : tabAt x = tabAtF x := by
  unfold tabAt tabAtF
  rw [trW_N0, trW_N1, trW_N2, trW_N3, trW_N4, trW_N5, trW_N6, trW_N7, trW_N8, trW_N9, trW_N10]

@[expose] noncomputable def tabSF (s : Nat) : Bool :=
  allN (nat_lit 2046) fun d => tabAtF (Nat.add (Nat.mul s (nat_lit 2046)) d)

theorem tabS_of_F (s : Nat) (h : tabSF s = true) : tabS s = true := by
  have e : (fun d => tabAt (Nat.add (Nat.mul s 2046) d)) =
      fun d => tabAtF (Nat.add (Nat.mul s 2046) d) := funext fun d => tabAt_eq_F _
  unfold tabS
  rw [e]
  exact h

end CertificateChecks.KernelSpor.ON3

end
