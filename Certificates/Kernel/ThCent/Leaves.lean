
module

public import Certificates.Kernel.ThCent.LeavesBase

public import CFSG.Sporadic.Th.KernelCentJ
public import Certificates.Kernel.ThCent.Assemble
public import Certificates.Kernel.ThCent.Shared
public import Certificates.Kernel.ThCent.C3A
public import Certificates.Kernel.ThCent.C3B
public import Certificates.Kernel.ThCent.C7A
public import Certificates.Kernel.ThCent.C7B
public import Certificates.Kernel.ThCent.C13A
public import Certificates.Kernel.ThCent.Wit
public import CFSG.Sporadic.Th.KernelCoset
public import CFSG.Sporadic.Th.LocalBase1
public import CFSG.Sporadic.Th.SimpleBase1

public section

namespace CertificateChecks.KernelThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.Sporadic.Bridge CFSG.KC.Th CFSG.KC.ThCent
  CFSG.KC.Th.Spec CFSG.KC.Th.Spec.DceStr CFSG.KD CFSG.KD.ThCent TauCeti

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem hNO : thcDceData.ThB_NO ≤ 2048 * 9 := by
  rw [thcDce_NO]
  decide

theorem class_T [Finite P] (hP : Nat.card P = thOrder) (hK : Nat.card K ≤ 634023936)
    {R H1 : ℕ → ℕ} {w FL CS CM : List ℕ} {o r i1 j1 Hi N1 m1 : ℕ}
    {OR1 OR2 OR3 OR4 OR5 OR6 OR7 OR8 OR9 OR10 : List ℕ}
    (hmisc : classMisc ThB.LT ThA.CB ThB.HB ThB.GB ThB.OB SV ThB.osh ThB.owd ThB.om ThB.NO
      w FL CS CM o r i1 j1 Hi N1 m1 = true)
    (hdiff : ∀ i < 9, diffChunk SV R H1 ThB.NO BF (psOf (wordM ThB.LT w) (Nat.sub o 1))
      (FL.map (DceS.mat ThA.CB)) i1 i = true)
    (hsel : ∀ i < 9, selChunk R ThB.NO CS i = true)
    (hcomm : ∀ i < 18, commChunk ThB.HB ThB.TB
      (mul24 (mul24 (gmN ThB.HB ThB.GB j1) (wordM ThB.LT w)) Hi) ThB.nT CM i = true)
    (h1 : ∀ i < 18, orChunk ThB.E1 36864 o r OR1 i = true)
    (h2 : ∀ i < 7, orChunk ThB.E2 13824 o r OR2 i = true)
    (h3 : ∀ i < 1, orChunk ThB.E3 486 o r OR3 i = true)
    (h4 : ∀ i < 1, orChunk ThB.E4 288 o r OR4 i = true)
    (h5 : ∀ i < 1, orChunk ThB.E5 54 o r OR5 i = true)
    (h6 : ∀ i < 1, orChunk ThB.E6 6 o r OR6 i = true)
    (h7 : ∀ i < 1, orChunk ThB.E7 126 o r OR7 i = true)
    (h8 : ∀ i < 1, orChunk ThB.E8 78 o r OR8 i = true)
    (h9 : ∀ i < 1, orChunk ThB.E9 72 o r OR9 i = true)
    (h10 : ∀ i < 2, orChunk ThB.E10 3528 o r OR10 i = true) :
    ∃ ht : wval gen w ∈ K, wval gen w ^ o = 1 ∧ (wval gen w = 1 → r = 0) ∧
      Nat.card (Subgroup.centralizer ({(⟨wval gen w, ht⟩ : K)} : Set K)) ≤ N1 * m1 ∧
      (∀ g ∈ K, ∀ w' : List ℕ, (∀ c ∈ w', c < 14) →
        g * wval gen w * g⁻¹ = wval gen w' → ordRank o r (wordM ThB.LT w') = true) ∧
      Nat.card {p : Om // (wval gen w : P) • p = p} ≤
        ∑ D', fixB (N1 * m1) (nOf OR1 OR2 OR3 OR4 OR5 OR6 OR7 OR8 OR9 OR10) D' := by
  have key := class_P hP hK thcDceData thcDce_chk hsh hNB hNO hnT hsv hpt
    (by rw [thcDce_LT, thcDce_CB, thcDce_HB, thcDce_GB, thcDce_OB, thcDce_osh, thcDce_owd,
      thcDce_om, thcDce_NO]; exact hmisc)
    (by rw [thcDce_NO, thcDce_LT, thcDce_CB]; exact hdiff) (by rw [thcDce_NO]; exact hsel)
    (by rw [thcDce_HB, thcDce_TB, thcDce_GB, thcDce_LT, thcDce_nT]; exact hcomm) _
    (or_counts h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
  rwa [thcDce_LT] at key

variable (h : KernelFacts)
include h

theorem hKc : Nat.card K = 634023936 := (isPreprimitive_Om h).2.2

theorem psi : ∃ ψ : P →* J, Function.Bijective ψ ∧
    (∀ g < 8, 𝕄 (ψ (presGen SporadicName.Th.presentation g)) =
        pkMat (thcFwdData.ThS_RBf (BigS.regAt thcFwdData.ThS_GRf g)) ∧
      𝕄 ((ψ (presGen SporadicName.Th.presentation g))⁻¹ : J) =
        pkMat (thcFwdData.ThS_RBf (BigS.regAt thcFwdData.ThS_IRf g))) ∧
    𝕄 a = pkMat (thcFwdData.ThS_RBf 1) ∧ 𝕄 b = pkMat (thcFwdData.ThS_RBf 2) ∧
    𝕄 (b⁻¹ : J) = pkMat thcFwdData.ThS_Bi ∧
    BigS.constsOK thcFwdData.ThS_c thcFwdData.ThS_rm thcFwdData.ThS_tm0 thcFwdData.ThS_tm1
      thcFwdData.ThS_tm2 thcFwdData.ThS_tm3 thcFwdData.ThS_tm4 thcFwdData.ThS_tm5
      thcFwdData.ThS_tm6 thcFwdData.ThS_tm7 thcFwdData.ThS_up thcFwdData.ThS_dg
      thcFwdData.ThS_ONE = true :=
  psi_of_fwd h thcFwdData thcFwd_chk (seedA_eq.symm.trans thcFwd_hA)
    (seedB_eq.symm.trans thcFwd_hB)

theorem conj_wit {ψ : P →* J}
    (hx : ∀ g < 8, 𝕄 (ψ (presGen SporadicName.Th.presentation g)) =
        pkMat (thcFwdData.ThS_RBf (BigS.regAt thcFwdData.ThS_GRf g)) ∧
      𝕄 ((ψ (presGen SporadicName.Th.presentation g))⁻¹ : J) =
        pkMat (thcFwdData.ThS_RBf (BigS.regAt thcFwdData.ThS_IRf g)))
    (hA : 𝕄 a = pkMat (thcFwdData.ThS_RBf 1)) (hB : 𝕄 b = pkMat (thcFwdData.ThS_RBf 2))
    (hBi : 𝕄 (b⁻¹ : J) = pkMat thcFwdData.ThS_Bi)
    (hk : BigS.constsOK thcFwdData.ThS_c thcFwdData.ThS_rm thcFwdData.ThS_tm0 thcFwdData.ThS_tm1
      thcFwdData.ThS_tm2 thcFwdData.ThS_tm3 thcFwdData.ThS_tm4 thcFwdData.ThS_tm5
      thcFwdData.ThS_tm6 thcFwdData.ThS_tm7 thcFwdData.ThS_up thcFwdData.ThS_dg
      thcFwdData.ThS_ONE = true)
    {Z hw hn tw tn : ℕ} {w : List ℕ}
    (hwit : witOK ThS.RBf ThS.c ThS.rm ThS.ONE ThS.Bi ThS.GRf ThS.IRf Z hw hn tw tn = true)
    (hd : codes4 tw tn = w) (z : J) (hz : 𝕄 z = pkMat Z) : IsConj z (ψ (wval gen w)) := by
  have hwit' : witOK thcFwdData.ThS_RBf thcFwdData.ThS_c thcFwdData.ThS_rm thcFwdData.ThS_ONE
      thcFwdData.ThS_Bi thcFwdData.ThS_GRf thcFwdData.ThS_IRf Z hw hn tw tn = true := by
    rw [thcFwd_RBf, thcFwd_c, thcFwd_rm, thcFwd_ONE, thcFwd_Bi, thcFwd_GRf, thcFwd_IRf]
    exact hwit
  have := conj_of_witOK (p := SporadicName.Th.presentation) a b ψ hk hx hA hB hBi hwit' z hz
  rwa [hd] at this

theorem card_centralizer_z3B_le (z : J) (hz : 𝕄 z = pkMat W.Z3B) :
    Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ 472392 := by
  have := h.finite
  obtain ⟨ψ, hψ, hx, hA, hB, hBi, hk⟩ := psi h
  obtain ⟨ht, -, -, hc, -, hfix⟩ := class_T (card_P_eq h) (hKc h).le C3B.misc C3B.diff.all
    C3B.sel.all C3B.comm.all C3B.or1.all C3B.or2.all C3B.or3.all C3B.or4.all C3B.or5.all
    C3B.or6.all C3B.or7.all C3B.or8.all C3B.or9.all C3B.or10.all
  have hz' := conj_wit h hx hA hB hBi hk W.w3B W.d3B z hz
  have key : Nat.card (Subgroup.centralizer ({z} : Set J)) *
      ∑ _i : Fin 1, 634023936 / (C3B.N1 * C3B.m1) ≤
        (∑ D', fixB (C3B.N1 * C3B.m1) (nOf C3B.OR1 C3B.OR2 C3B.OR3 C3B.OR4 C3B.OR5 C3B.OR6
          C3B.OR7 C3B.OR8 C3B.OR9 C3B.OR10) D') * 634023936 :=
    card_centralizer_mul_le_of_conj (hKc h) (fun _ => ⟨wval gen C3B.word, ht⟩)
      (fun _ => C3B.N1 * C3B.m1) (fun _ => hc) (fun i j hij => absurd (Subsingleton.elim i j) hij)
      0 hfix ψ hψ z fun _ => hz'
  rw [show ∑ _i : Fin 1, 634023936 / (C3B.N1 * C3B.m1) = 326144 by decide +kernel,
    show ∑ D', fixB (C3B.N1 * C3B.m1) (nOf C3B.OR1 C3B.OR2 C3B.OR3 C3B.OR4 C3B.OR5 C3B.OR6
      C3B.OR7 C3B.OR8 C3B.OR9 C3B.OR10) D' = 243 by decide +kernel] at key
  omega

theorem card_centralizer_z3A_le (z : J) (hz : 𝕄 z = pkMat W.Z3A) :
    Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ 15921360 := by
  have := h.finite
  obtain ⟨ψ, hψ, hx, hA, hB, hBi, hk⟩ := psi h
  obtain ⟨ht, -, -, hc, -, hfix⟩ := class_T (card_P_eq h) (hKc h).le C3A.misc C3A.diff.all
    C3A.sel.all C3A.comm.all C3A.or1.all C3A.or2.all C3A.or3.all C3A.or4.all C3A.or5.all
    C3A.or6.all C3A.or7.all C3A.or8.all C3A.or9.all C3A.or10.all
  have hz' := conj_wit h hx hA hB hBi hk W.w3A W.d3A z hz
  have key : Nat.card (Subgroup.centralizer ({z} : Set J)) *
      ∑ _i : Fin 1, 634023936 / (C3A.N1 * C3A.m1) ≤
        (∑ D', fixB (C3A.N1 * C3A.m1) (nOf C3A.OR1 C3A.OR2 C3A.OR3 C3A.OR4 C3A.OR5 C3A.OR6
          C3A.OR7 C3A.OR8 C3A.OR9 C3A.OR10) D') * 634023936 :=
    card_centralizer_mul_le_of_conj (hKc h) (fun _ => ⟨wval gen C3A.word, ht⟩)
      (fun _ => C3A.N1 * C3A.m1) (fun _ => hc) (fun i j hij => absurd (Subsingleton.elim i j) hij)
      0 hfix ψ hψ z fun _ => hz'
  rw [show ∑ _i : Fin 1, 634023936 / (C3A.N1 * C3A.m1) = 139776 by decide +kernel,
    show ∑ D', fixB (C3A.N1 * C3A.m1) (nOf C3A.OR1 C3A.OR2 C3A.OR3 C3A.OR4 C3A.OR5 C3A.OR6
      C3A.OR7 C3A.OR8 C3A.OR9 C3A.OR10) D' = 3510 by decide +kernel] at key
  omega

theorem card_centralizer_z7_le (z : J) (hz : 𝕄 z = pkMat W.Z7) :
    Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ 1176 := by
  have := h.finite
  obtain ⟨ψ, hψ, hx, hA, hB, hBi, hk⟩ := psi h
  obtain ⟨htA, -, -, hcA, hinvA, hfixA⟩ := class_T (card_P_eq h) (hKc h).le C7A.misc C7A.diff.all
    C7A.sel.all C7A.comm.all C7A.or1.all C7A.or2.all C7A.or3.all C7A.or4.all C7A.or5.all
    C7A.or6.all C7A.or7.all C7A.or8.all C7A.or9.all C7A.or10.all
  obtain ⟨htB, -, -, hcB, hinvB, -⟩ := class_T (card_P_eq h) (hKc h).le C7B.misc C7B.diff.all
    C7B.sel.all C7B.comm.all C7B.or1.all C7B.or2.all C7B.or3.all C7B.or4.all C7B.or5.all
    C7B.or6.all C7B.or7.all C7B.or8.all C7B.or9.all C7B.or10.all
  have hzA := conj_wit h hx hA hB hBi hk W.w7A W.d7A z hz
  have hzB := conj_wit h hx hA hB hBi hk W.w7B W.d7B z hz
  have mA := Gen.andB_left C7A.misc
  have mB := Gen.andB_left C7B.misc
  have hwA := allLt_spec (Gen.andB_left (Gen.andB_left mA))
  have hwB := allLt_spec (Gen.andB_left (Gen.andB_left mB))
  have hrA : ordRank 7 18 (wordM ThB.LT C7A.word) = true := Gen.andB_right (Gen.andB_left mA)
  have hrB : ordRank 7 24 (wordM ThB.LT C7B.word) = true := Gen.andB_right (Gen.andB_left mB)
  have hsd : ∀ i j : Fin 2, i ≠ j →
      ¬IsConj (![⟨wval gen C7A.word, htA⟩, ⟨wval gen C7B.word, htB⟩] i : K)
        (![⟨wval gen C7A.word, htA⟩, ⟨wval gen C7B.word, htB⟩] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact not_conj_of_rank (by decide +kernel) htA htB hinvA hwB hrB
    · exact fun hc => not_conj_of_rank (by decide +kernel) htA htB hinvA hwB hrB hc.symm
    · exact absurd rfl hij
  have key : Nat.card (Subgroup.centralizer ({z} : Set J)) *
      ∑ i : Fin 2, 634023936 / (![C7A.N1 * C7A.m1, C7B.N1 * C7B.m1] i) ≤
        (∑ D', fixB (C7A.N1 * C7A.m1) (nOf C7A.OR1 C7A.OR2 C7A.OR3 C7A.OR4 C7A.OR5 C7A.OR6
          C7A.OR7 C7A.OR8 C7A.OR9 C7A.OR10) D') * 634023936 :=
    card_centralizer_mul_le_of_conj (hKc h)
      ![⟨wval gen C7A.word, htA⟩, ⟨wval gen C7B.word, htB⟩] ![C7A.N1 * C7A.m1, C7B.N1 * C7B.m1]
      (fun i => by fin_cases i; exacts [hcA, hcB]) hsd 0 hfixA ψ hψ z
      (fun i => by fin_cases i; exacts [hzA, hzB])
  rw [show ∑ i : Fin 2, 634023936 / (![C7A.N1 * C7A.m1, C7B.N1 * C7B.m1] i) = 4852224 by
      decide +kernel,
    show ∑ D', fixB (C7A.N1 * C7A.m1) (nOf C7A.OR1 C7A.OR2 C7A.OR3 C7A.OR4 C7A.OR5 C7A.OR6
      C7A.OR7 C7A.OR8 C7A.OR9 C7A.OR10) D' = 9 by decide +kernel] at key
  omega

theorem card_centralizer_13_le (z : J) (hz : orderOf z = 13) :
    Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ 39 := by
  have := h.finite
  have hJc := card_J_eq h
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [hJc]; decide)
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ, -⟩ := psi h
  obtain ⟨ht, hpow, h1, hc, -, hfix⟩ := class_T (card_P_eq h) (hKc h).le C13A.misc C13A.diff.all
    C13A.sel.all C13A.comm.all C13A.or1.all C13A.or2.all C13A.or3.all C13A.or4.all C13A.or5.all
    C13A.or6.all C13A.or7.all C13A.or8.all C13A.or9.all C13A.or10.all
  set y := ψ (wval gen C13A.word) with hy
  have key : Nat.card (Subgroup.centralizer ({y} : Set J)) *
      ∑ _i : Fin 1, 634023936 / (C13A.N1 * C13A.m1) ≤
        (∑ D', fixB (C13A.N1 * C13A.m1) (nOf C13A.OR1 C13A.OR2 C13A.OR3 C13A.OR4 C13A.OR5
          C13A.OR6 C13A.OR7 C13A.OR8 C13A.OR9 C13A.OR10) D') * 634023936 :=
    card_centralizer_mul_le_of_conj (hKc h) (fun _ => ⟨wval gen C13A.word, ht⟩)
      (fun _ => C13A.N1 * C13A.m1) (fun _ => hc) (fun i j hij => absurd (Subsingleton.elim i j) hij)
      0 hfix ψ hψ y fun _ => IsConj.refl _
  rw [show ∑ _i : Fin 1, 634023936 / (C13A.N1 * C13A.m1) = 48771072 by decide +kernel,
    show ∑ D', fixB (C13A.N1 * C13A.m1) (nOf C13A.OR1 C13A.OR2 C13A.OR3 C13A.OR4 C13A.OR5
      C13A.OR6 C13A.OR7 C13A.OR8 C13A.OR9 C13A.OR10) D' = 3 by decide +kernel] at key
  have hcy : Nat.card (Subgroup.centralizer ({y} : Set J)) ≤ 39 := by omega
  have hy13 : y ^ 13 = 1 := by
    have e : wval gen C13A.word ^ 13 = 1 := hpow
    rw [hy, ← map_pow, e, map_one]
  have hy1 : y ≠ 1 := by
    intro e
    have e2 : wval gen C13A.word = 1 := hψ.1 (e.trans (map_one ψ).symm)
    exact absurd (h1 e2) (by decide +kernel)
  have hoy : orderOf y = 13 := orderOf_eq_prime hy13 hy1
  have hfac : (Nat.card J).factorization 13 = 1 := by
    rw [hJc, show thOrder = 13 * 6980457222144000 by norm_num [thOrder],
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  exact (card_centralizer_le_of_sylow hfac hoy hz).trans hcy

end CertificateChecks.KernelThCent

end
