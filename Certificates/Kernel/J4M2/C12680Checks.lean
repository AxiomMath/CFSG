module

public import Certificates.Data.Kernel.J4SlpSparse
public import Certificates.Kernel.J4M2.C12607Checks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.GenData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.GenData
public meta import Certificates.Kernel.SporSch.J4S.Gen
public import Certificates.Kernel.Misc.Perm.CharsCat
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC12680

open CFSG.AGLEmbeddingD2.Wilson.Coordinator CFSG.Sporadic.J4Schreier in
meta def pairs12680 : Array Pair :=
  #[xJn 0, xJn 1, xJn 2, gamN] ++ xN.toArray ++ (xN.map g2N).toArray

end CertificateChecks.KernelC12680

#kss_pairs CertificateChecks.KernelC12680.PL CertificateChecks.KernelC12680.pairs12680
#ks_chars_cat CertificateChecks.KernelC12680.T0 CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpText0
#ks_chars_cat CertificateChecks.KernelC12680.T1 CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpText1
#ks_chars_cat CertificateChecks.KernelC12680.T2 CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpText2
#ks_chars_cat CertificateChecks.KernelC12680.T3 CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpText3
#ks_chars_cat CertificateChecks.KernelC12680.T4 CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpText4
#ks_chars_cat CertificateChecks.KernelC12680.T5 CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpText5
#ks_chars_cat CertificateChecks.KernelC12680.T6 CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpText6
#ks_chars_cat CertificateChecks.KernelC12680.T7 CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpText7

namespace CertificateChecks.KernelC12680

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KC.Loop CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KC.J4Sp
  CertificateChecks.KernelSporSch.J4E7 CertificateChecks.KernelJ4Gam

@[expose] noncomputable def P (k : Nat) : Nat × Nat := (getN one PL k, getN one PL (Nat.add 20 k))

@[expose] noncomputable def XJF (k : Nat) : Nat × Nat :=
  wordQ c rm one [A, B] [A, Bi] (CFSG.Sporadic.J4.Native.localWords.getD k [])

@[expose] noncomputable def FS : List Nat := [(P 0).1, (P 1).1, (P 2).1, A, B]

@[expose] noncomputable def SS : List Nat := [(P 0).2, (P 1).2, (P 2).2, A, Bi]

@[expose] noncomputable def GE (n : Nat) : Nat × Nat :=
  wordQ c rm one FS SS (CFSG.Quasithin.J4M2.genWord n)

@[expose] noncomputable def UQ (j : Nat) : Nat × Nat :=
  wordQ c rm one [(P 0).1, (P 1).1, (P 2).1] [(P 0).2, (P 1).2, (P 2).2]
    (CFSG.Sporadic.J4.QT.uWord j)

@[expose] noncomputable def HW : Nat × Nat :=
  wordQ c rm one [A, B] [A, Bi] CFSG.AGLEmbeddingD2.Wilson.Coordinator.hWordN

@[expose] noncomputable def GF : Nat × Nat :=
  mP (pP (mP (etaQ c rm one UQ 11 1131) (mP (mP HW (pP H2 20)) (iP HW))) 6) HW

@[expose] noncomputable def XF (i : Nat) : Nat × Nat :=
  if i = 0 then GE 0 else if i = 1 then GE 1 else if i = 2 then mP (GE 0) (GE 2)
  else if i = 3 then mP (GE 1) (GE 2) else if i = 4 then mP (mP (GE 0) (GE 1)) (GE 2)
  else if i = 5 then mP (GE 1) (GE 3) else if i = 6 then mP (GE 2) (GE 3)
  else mP (mP (mP (mP (mP (GE 15) (GE 29)) (GE 1)) (GE 7)) (GE 9)) (GE 11)

@[expose] noncomputable def G2F (i : Nat) : Nat × Nat :=
  mP H1 (mP (mP (iP (P 3)) (P (Nat.add 4 i))) (P 3))

@[expose] noncomputable def runC (i : Nat) (cs : List Char) : Bool :=
  slpT c rm one (CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpN.getD i 0)
    (CFSG.AGLEmbeddingD2.Wilson.Coordinator.slpK.getD i 0) B cs H2.1 H2.2
    (P (Nat.add 12 i)).1 (P (Nat.add 12 i)).2

theorem c12680_xj : andB (eqP (P 0) (XJF 0)) (andB (eqP (P 1) (XJF 1)) (eqP (P 2) (XJF 2))) =
    true := by quickRfl

theorem c12680_gam : eqP (P 3) GF = true := by quickRfl

theorem c12680_x : (List.range 8).all (fun i => eqP (P (Nat.add 4 i)) (XF i)) = true := by
  quickRfl

theorem c12680_g2 : (List.range 8).all (fun i => eqP (P (Nat.add 12 i)) (G2F i)) = true := by
  quickRfl

theorem c12680_run0 : runC 0 T0.chars = true := by quickRfl
theorem c12680_run1 : runC 1 T1.chars = true := by quickRfl
theorem c12680_run2 : runC 2 T2.chars = true := by quickRfl
theorem c12680_run3 : runC 3 T3.chars = true := by quickRfl
theorem c12680_run4 : runC 4 T4.chars = true := by quickRfl
theorem c12680_run5 : runC 5 T5.chars = true := by quickRfl
theorem c12680_run6 : runC 6 T6.chars = true := by quickRfl
theorem c12680_run7 : runC 7 T7.chars = true := by quickRfl

theorem c12680_conj : andB
    (Nat.beq (mulJ c rm A (V 3).1) (mulJ c rm (mP (mP (pP (V 3) 10) (pP (V 4) 0)) (pP (V 5) 1)).1 A))
    (Nat.beq (mulJ c rm A (V 4).1) (mulJ c rm (mP (mP (pP (V 3) 0) (pP (V 4) 10)) (pP (V 5) 6)).1 A))
    = true := by quickRfl

theorem c12680_neg : andB (notB (slpT c rm one 759 757 B T2.chars H2.1 H2.2 (P 14).1 (P 14).2))
    (andB (notB (slpT c rm one 759 758 B T2.chars H2.1 H2.2 (P 17).1 (P 17).2))
      (notB (slpT c rm one 759 758 A T2.chars H2.1 H2.2 (P 14).1 (P 14).2))) = true := by
  quickRfl

end CertificateChecks.KernelC12680

end
