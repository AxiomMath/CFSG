
module

public import Certificates.Kernel.SporSch.J4S.Eta
public import Certificates.Kernel.SporSch.J4S.Three
public import CFSG.Certificates.Kernel.SporSch.J4SGetSound
public import CFSG.Sporadic.Schreier.J4SRankData
meta import Certificates.Kernel.SporSch.J4S.Q3Data
import CFSG.Certificates.Kernel.Common.Harness
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
public import CFSG.Sporadic.Schreier.J4SThreeDataBase
meta import CFSG.Sporadic.Schreier.J4SThreeDataBase

public section

set_option maxRecDepth 400000

#kss_pairs CertificateChecks.KernelSporSch.J4S0 CertificateChecks.KernelSporSch.J4Rank.q3Suf0
#kss_pairs CertificateChecks.KernelSporSch.J4S1 CertificateChecks.KernelSporSch.J4Rank.q3Suf1
#kss_pairs CertificateChecks.KernelSporSch.J4KP CFSG.Sporadic.J4Schreier.Q3GenPairs
#kss_pairs CertificateChecks.KernelSporSch.J4QE CertificateChecks.KernelSporSch.J4Rank.q3Elts
#kss_pairs CertificateChecks.KernelSporSch.J4ER CertificateChecks.KernelSporSch.J4Rank.etaRows

namespace CertificateChecks.KernelSporSch.J4Rank

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta

@[expose] noncomputable def segK (w : List Int) (T : List Nat) (k : Nat) : Bool :=
  bAnd(Nat.beq (wFK c rm one (R 1) (R 10) (R 2) (R 11) (takeI 100 (dropI (Nat.mul 100 k) w))
      (getN one T (Nat.succ k))) (getN one T k),
    Nat.beq (wSK c rm one (R 1) (R 10) (R 2) (R 11) (takeI 100 (dropI (Nat.mul 100 k) w))
      (getN one T (Nat.add 10 k))) (getN one T (Nat.add 9 k)))

@[expose] noncomputable def seg0 (k : Nat) : Bool := segK J4Q3T.w0 J4S0 k
@[expose] noncomputable def seg1 (k : Nat) : Bool := segK J4Q3T.w1 J4S1 k

@[expose] noncomputable def QF (k : Nat) : Nat := getN one J4QE k
@[expose] noncomputable def QS (k : Nat) : Nat := getN one J4QE (Nat.add 27 k)

@[expose] noncomputable def p0 (k : Nat) : Nat := CFSG.KS.SporSch.C11.ent 5 (J4Q3P k) 0
@[expose] noncomputable def p1 (k : Nat) : Nat := CFSG.KS.SporSch.C11.ent 5 (J4Q3P k) 1

@[expose] noncomputable def eltK (k : Nat) : Bool :=
  bIf(Nat.beq k 0, bAnd(Nat.beq (QF 0) one, Nat.beq (QS 0) one),
    bAnd(Nat.blt (p0 k) k, bAnd(Nat.blt (p1 k) 2,
      bAnd(Nat.beq (mulJ c rm (QF (p0 k)) (getN one J4KP (p1 k))) (QF k),
        Nat.beq (mulJ c rm (getN one J4KP (Nat.add 2 (p1 k))) (QS (p0 k))) (QS k)))))

@[expose] noncomputable def rowsK (P : Nat) : Bool := rows3OK #[rowJ rm P 0, rowJ rm P 1, rowJ rm P 2]

end CertificateChecks.KernelSporSch.J4Rank

#kss_slices CertificateChecks.KernelSporSch.J4Seg0 CertificateChecks.KernelSporSch.J4Rank.seg0 1 8
#kss_slices CertificateChecks.KernelSporSch.J4Seg1 CertificateChecks.KernelSporSch.J4Rank.seg1 1 8

namespace CertificateChecks.KernelSporSch.J4Rank

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta

theorem b0a : Nat.beq (getN one J4S0 8) one = true := by quickRfl
theorem b0b : Nat.beq (getN one J4S0 17) one = true := by quickRfl
theorem b1a : Nat.beq (getN one J4S1 8) one = true := by quickRfl
theorem b1b : Nat.beq (getN one J4S1 17) one = true := by quickRfl

theorem g0a : Nat.beq (powJ c rm one (getN one J4S0 0) 4) (getN one J4KP 0) = true := by quickRfl
theorem g0b : Nat.beq (powJ c rm one (getN one J4S0 9) 4) (getN one J4KP 2) = true := by quickRfl
theorem g1a : Nat.beq (powJ c rm one (getN one J4S1 0) 2) (getN one J4KP 1) = true := by quickRfl
theorem g1b : Nat.beq (powJ c rm one (getN one J4S1 9) 2) (getN one J4KP 3) = true := by quickRfl

theorem elt : allN 27 eltK = true := by quickRfl

theorem rowsQ : allN 26 (fun k => rowsK (QF (Nat.succ k))) = true := by quickRfl

theorem e1 : Nat.beq (prodFK c rm one (ef 1)) (getN one J4ER 0) = true := by quickRfl
theorem e14 : Nat.beq (prodFK c rm one (ef 14)) (getN one J4ER 1) = true := by quickRfl
theorem r1 : rowsK (getN one J4ER 0) = true := by quickRfl
theorem r14 : rowsK (getN one J4ER 1) = true := by quickRfl

theorem letters0 : ∀ l ∈ J4Q3T.w0, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by decide +kernel
theorem letters1 : ∀ l ∈ J4Q3T.w1, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by decide +kernel
theorem len0 : J4Q3T.w0.length ≤ 800 := by decide +kernel
theorem len1 : J4Q3T.w1.length ≤ 800 := by decide +kernel

end CertificateChecks.KernelSporSch.J4Rank

end
