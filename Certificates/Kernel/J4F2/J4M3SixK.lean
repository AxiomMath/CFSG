module

public import Certificates.Kernel.J4F2.J4M3Three
public import Certificates.Kernel.J4Q.LocM
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2 CertificateChecks.KernelJ4Q CFSG.Quasithin.J4M3

@[expose] noncomputable def m3U : Nat := getN one MLs 4

@[expose] noncomputable def m3Ui : Nat := getN one MLIs 4

@[expose] noncomputable def m3N : Nat :=
  mulJ c rm (mulJ c rm (wK (invWord nWordL)) m3U) (wK (invWord nWordR))

@[expose] noncomputable def m3Ni : Nat := mulJ c rm (mulJ c rm (wK nWordR) m3Ui) (wK nWordL)

@[expose] noncomputable def m3Pt (m : Nat) : Nat := vecJ rm (v2N rootV) (mulJ c rm m3Ni (eK m))

@[expose] noncomputable def m3Norm (N Ni : Nat) : Bool :=
  v0Gens.all fun m => v0Masks.any fun d => Nat.beq (mulJ c rm (mulJ c rm N (eK m)) Ni) (eK d)

@[expose] noncomputable def m3Fix (P : Nat) : Bool :=
  ptMasks.all fun m => Nat.beq (vecJ rm (m3Pt m) P) (m3Pt m)

@[expose] noncomputable def m3Cent (P : Nat) : Bool :=
  v0Gens.all fun m => Nat.beq (mulJ c rm P (eK m)) (mulJ c rm (eK m) P)

@[expose] noncomputable def m3Diff (a b : Nat) : Bool :=
  (List.range 112).any fun i => neN (rowJ (2 ^ 112 - 1) a i) (rowJ (2 ^ 112 - 1) b i)

theorem m3_n : m3Norm m3N m3Ni = true := by quickRfl

theorem m3_pts : (ptMasks.all (fun m => neN (m3Pt m) (v2N rootV)) &&
    ptMasks.all fun m => ptMasks.all fun d => m == d || neN (m3Pt m) (m3Pt d)) = true := by
  quickRfl

theorem m3_p : (((List.range 12).all fun i => m3Fix (pK i) && m3Cent (pK i)) &&
    m3Fix (wK xWord) && m3Norm (wK xWord) (wK (invWord xWord)) &&
    m3Diff (mulJ c rm (mulJ c rm (wK xWord) (eK 1131)) (wK (invWord xWord))) (eK 1131)) = true := by
  quickRfl

theorem m3_q : ((List.range 12).all fun i =>
    Nat.beq (mulJ c rm (commK (pK i) (wK xWord) (piK i) (wK (invWord xWord)))
        (commK (pK i) (wK xWord) (piK i) (wK (invWord xWord)))) (eK (sqTab.getD i 0)) &&
      (List.range 12).all fun j =>
        Nat.beq (commK (commK (pK i) (wK xWord) (piK i) (wK (invWord xWord)))
            (commK (pK j) (wK xWord) (piK j) (wK (invWord xWord)))
            (commK (wK xWord) (pK i) (wK (invWord xWord)) (piK i))
            (commK (wK xWord) (pK j) (wK (invWord xWord)) (piK j)))
          (eK ((commTab.getD i []).getD j 0))) = true := by
  quickRfl

theorem m3_c : (m3Cent (wK cWord) && Nat.beq (vecJ rm (m3Pt 0) (wK cWord)) (m3Pt 0) &&
    Nat.beq (vecJ rm (m3Pt 1) (wK cWord)) (m3Pt 1) &&
    Nat.beq (vecJ rm (m3Pt 16) (wK cWord)) (m3Pt 17) &&
    Nat.beq (vecJ rm (m3Pt 17) (wK cWord)) (m3Pt 16)) = true := by
  quickRfl

end CertificateChecks.KernelJ4F2

end
