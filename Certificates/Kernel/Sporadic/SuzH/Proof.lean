module

public import Certificates.Kernel.Sporadic.SuzH.Checks
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps

public section

namespace CertificateChecks.KernelSpor.SuzH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native
open CFSG.Sporadic.SuzI301Cover.Native CFSG.Sporadic.SuzI301
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.Sporadic.SuzOddCore

theorem hw : szOK 1782 11 = true := rfl

theorem permX {i : Nat} (hi : i < 3) : permB 1782 11 (X i) = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  interval_cases i
  · exact h.1.1.1.1
  · exact h.1.1.1.2
  · exact h.1.1.2

theorem permN {k : Nat} (hk : k < 2) : permB 1782 11 (SuzHN.F k) = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  interval_cases k
  · exact h.1.2
  · exact h.2

theorem bArr_eq {i : Nat} (hi : i < 3) : bArr i = unpack 1782 11 (X i) := by
  interval_cases i
  · rw [bArr, if_pos rfl, sD]
    exact suzArr_eq (k := 1) (by norm_num)
  · rw [bArr, if_neg (by decide), if_pos rfl, sB2]
    exact suzArr_eq (k := 2) (by norm_num)
  · rw [bArr, if_neg (by decide), if_neg (by decide), sB3]
    exact suzArr_eq (k := 3) (by norm_num)

theorem valid_of {p : Nat} (hp : permB 1782 11 p = true) : validA 1782 (unpack 1782 11 p) = true :=
  validA_unpack hp

theorem inP_of {k : Nat} (hk : k < 2) (hs : siftS (SuzHN.F k) = true) :
    inP (levels ()) (nArr k) = true := by
  have hc := (pp_of_permB hw (permN hk)).1
  have e := CertificateChecks.KernelSpor.OddCore.inM_eq (nArr_eq hk) hc
  change inM (nArr k) = true
  rw [e]
  exact hs

theorem conj_eq {N A B C D : Nat} (hN : permB 1782 11 N = true) (hA : permB 1782 11 A = true)
    (hB : permB 1782 11 B = true) (hC : permB 1782 11 C = true) (hD : permB 1782 11 D = true)
    (a b c : Nat) :
    eqA 1782 (conj1782 (unpack 1782 11 N) (invCand 1782 (unpack 1782 11 N)) (unpack 1782 11 D))
      (compA 1782 (powArr 1782 (unpack 1782 11 A) a) (compA 1782 (powArr 1782 (unpack 1782 11 B) b)
        (powArr 1782 (unpack 1782 11 C) c))) =
      Nat.beq (pc3 N D (pinvS 1782 11 (mask 11) N)) (pc3 (pw A a) (pw B b) (pw C c)) := by
  have hNi := permB_pinvS hw hN
  have hDN := permB_pcomp hw hD hNi
  have hb := permB_ppow hw hB b
  have hc := permB_ppow hw hC c
  have hbc := permB_pcomp hw hb hc
  unfold conj1782
  rw [invCand_PP (pp_of_permB hw hN), comp_unpack' hw hD hNi, comp_unpack' hw hN hDN,
    pow_unpack' hw hA, pow_unpack' hw hB, pow_unpack' hw hC, comp_unpack' hw hb hc,
    comp_unpack' hw (permB_ppow hw hA a) hbc,
    eqA_unpack' hw (permB_pcomp hw hN hDN) (permB_pcomp hw (permB_ppow hw hA a) hbc)]
  rfl

theorem conjOK_of {k i : Nat} (hk : k < 2) (hi : i < 3) (h : conjK k i = true) :
    conjOK k i = true := by
  unfold conjOK prodArr
  rw [nArr_eq hk, bArr_eq hi, bArr_eq (i := 0) (by norm_num), bArr_eq (i := 1) (by norm_num),
    bArr_eq (i := 2) (by norm_num),
    conj_eq (permN hk) (permX (by norm_num)) (permX (by norm_num)) (permX (by norm_num)) (permX hi)]
  exact h

theorem suzh_check : suzhCheck () = true := by
  have vb : ∀ i < 3, validA 1782 (bArr i) = true := fun i hi => by
    rw [bArr_eq hi]
    exact valid_of (permX hi)
  have vn : ∀ k < 2, validA 1782 (nArr k) = true := fun k hk => by
    rw [nArr_eq hk]
    exact valid_of (permN hk)
  have v0 := vb 0 (by norm_num)
  have v1 := vb 1 (by norm_num)
  have v2 := vb 2 (by norm_num)
  have n0 := vn 0 (by norm_num)
  have n1 := vn 1 (by norm_num)
  have i0 := inP_of (k := 0) (by norm_num) kSift0
  have i1 := inP_of (k := 1) (by norm_num) kSift1
  have c00 := conjOK_of (k := 0) (i := 0) (by norm_num) (by norm_num) kConj00
  have c01 := conjOK_of (k := 0) (i := 1) (by norm_num) (by norm_num) kConj01
  have c02 := conjOK_of (k := 0) (i := 2) (by norm_num) (by norm_num) kConj02
  have c10 := conjOK_of (k := 1) (i := 0) (by norm_num) (by norm_num) kConj10
  have c11 := conjOK_of (k := 1) (i := 1) (by norm_num) (by norm_num) kConj11
  have c12 := conjOK_of (k := 1) (i := 2) (by norm_num) (by norm_num) kConj12
  unfold suzhCheck
  simp only [v0, v1, v2, n0, n1, i0, i1, c00, c01, c02, c10, c11, c12, Bool.and_self]

@[expose] def altM (a b c : ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![0, a, b; -a, 0, c; -b, -c, 0]

theorem alt_key : ∀ a b c : ZMod 3, (∀ k : Fin 2, nMat k * altM a b c * (nMat k).transpose =
    altM a b c) → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel

theorem alt_zero : ∀ C : Matrix (Fin 3) (Fin 3) (ZMod 3), (∀ i, C i i = 0) →
    (∀ i j, C j i = -C i j) → (∀ k : Fin 2, nMat k * C * (nMat k).transpose = C) → C = 0 := by
  intro C hd ha hk
  have e10 := ha 0 1
  have e20 := ha 0 2
  have e21 := ha 1 2
  have hC : C = altM (C 0 1) (C 0 2) (C 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [altM, hd, e10, e20, e21]
  rw [hC] at hk
  obtain ⟨h1, h2, h3⟩ := alt_key _ _ _ hk
  rw [hC, h1, h2, h3]
  decide +kernel

theorem fix_zero : ∀ q : Fin 3 → ZMod 3, (∀ k : Fin 2, (nMat k).mulVec q = q) → q = 0 := by
  decide +kernel

end CertificateChecks.KernelSpor.SuzH

end
