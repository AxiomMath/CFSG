module

public import CFSG.Sporadic.Th.KernelCentOuter
public import Certificates.Kernel.ThCent.Leaves
public import Certificates.Kernel.ThCent.C3C
public import Certificates.Kernel.ThCent.C3D
public import Certificates.Kernel.ThCent.Wit3C
public import CFSG.Certificates.Kernel.ThCent.PinSound
public import Certificates.Kernel.ThCent.Consumers

public section

namespace CertificateChecks.KernelThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.Sporadic.Bridge CFSG.KC.Th CFSG.KC.ThCent
  CFSG.KC.Th.Spec CFSG.KC.Th.Spec.DceStr CFSG.KD CFSG.KD.ThCent TauCeti
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem class_C [Finite P] (hP : Nat.card P = thOrder) (hK : Nat.card K ≤ 634023936)
    {R H1 : ℕ → ℕ} {w FL CS CM : List ℕ} {o r i1 j1 Hi N1 m1 : ℕ}
    (hmisc : classMisc ThB.LT ThA.CB ThB.HB ThB.GB ThB.OB SV ThB.osh ThB.owd ThB.om ThB.NO
      w FL CS CM o r i1 j1 Hi N1 m1 = true)
    (hdiff : ∀ i < 9, diffChunk SV R H1 ThB.NO BF (psOf (wordM ThB.LT w) (Nat.sub o 1))
      (FL.map (DceS.mat ThA.CB)) i1 i = true)
    (hsel : ∀ i < 9, selChunk R ThB.NO CS i = true)
    (hcomm : ∀ i < 18, commChunk ThB.HB ThB.TB
      (mul24 (mul24 (gmN ThB.HB ThB.GB j1) (wordM ThB.LT w)) Hi) ThB.nT CM i = true) :
    ∃ ht : wval gen w ∈ K,
      Nat.card (Subgroup.centralizer ({(⟨wval gen w, ht⟩ : K)} : Set K)) ≤ N1 * m1 := by
  obtain ⟨ht, -, -, hc, -, -⟩ := class_P hP hK thcDceData thcDce_chk hsh hNB hNO hnT hsv hpt
    (by rw [thcDce_LT, thcDce_CB, thcDce_HB, thcDce_GB, thcDce_OB, thcDce_osh, thcDce_owd,
      thcDce_om, thcDce_NO]; exact hmisc)
    (by rw [thcDce_NO, thcDce_LT, thcDce_CB]; exact hdiff) (by rw [thcDce_NO]; exact hsel)
    (by rw [thcDce_HB, thcDce_TB, thcDce_GB, thcDce_LT, thcDce_nT]; exact hcomm) mD
    (fun D' _ => (Finset.card_filter_le _ _).trans (Finset.card_range _).le)
  exact ⟨ht, hc⟩

@[expose] noncomputable def nOut : Fin 11 → ℕ :=
  ![0, sumN C3C.OJ5 - C3C.MK5.length, sumN C3C.OJ7 - C3C.MK7.length,
    sumN C3C.OJ6 - C3C.MK6.length, sumN C3C.OJ9 - C3C.MK9.length, sumN C3C.OJ8 - C3C.MK8.length,
    sumN C3C.OJ3 - C3C.MK3.length, sumN C3C.OJ2 - C3C.MK2.length, sumN C3C.OJ4 - C3C.MK4.length,
    sumN C3C.OJ10 - C3C.MK10.length, sumN C3C.OJ1 - C3C.MK1.length]

theorem out_counts : ∀ D' : Fin 11, D' ≠ 0 → ((Finset.range (mD D')).filter fun j =>
    outerQ thcDceData.ThA_CB C3C.MU C3C.o C3C.r
      (DceS.mat (tabB thcDceData (cosetOrder D')) j) = true).card ≤ nOut D' := by
  intro D' hD0
  fin_cases D' <;>
    simp only [nOut, tabB, cosetOrder, thcDce_E1, thcDce_E2, thcDce_E3, thcDce_E4, thcDce_E5,
      thcDce_E6, thcDce_E7, thcDce_E8, thcDce_E9, thcDce_E10, thcDce_CB, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val, ne_eq] at hD0 ⊢
  · exact absurd trivial hD0
  · exact outerQ_card_le (by decide) C3C.oj5.all C3C.mk5
  · exact outerQ_card_le (by decide) C3C.oj7.all C3C.mk7
  · exact outerQ_card_le (by decide) C3C.oj6.all C3C.mk6
  · exact outerQ_card_le (by decide) C3C.oj9.all C3C.mk9
  · exact outerQ_card_le (by decide) C3C.oj8.all C3C.mk8
  · exact outerQ_card_le (by decide) C3C.oj3.all C3C.mk3
  · exact outerQ_card_le (by decide) C3C.oj2.all C3C.mk2
  · exact outerQ_card_le (by decide) C3C.oj4.all C3C.mk4
  · exact outerQ_card_le (by decide) C3C.oj10.all C3C.mk10
  · exact outerQ_card_le (by decide) C3C.oj1.all C3C.mk1


theorem mat_u :
    𝕄 (slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22) = pkMat W3.Z3C := by
  obtain ⟨hA, hB, -, hk⟩ := fwd_mats
  rw [← Nat.eq_of_beq_eq_true W3.u3C, pkMat_runPk hk _ (by decide +kernel) _ _
    (pkMat_initPk hk a b hA hB), slpJ_eq]
  rfl

variable (h : KernelFacts)
include h

theorem card_centralizer_z3C_le (z : J) (hz : 𝕄 z = pkMat W3.Z3C) :
    Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ 174960 := by
  have := h.finite
  obtain ⟨ψ, hψ, hx, hA, hB, hBi, hk⟩ := psi h
  obtain ⟨htC, hcC⟩ := class_C (card_P_eq h) (hKc h).le C3C.misc C3C.diff.all C3C.sel.all
    C3C.comm.all
  obtain ⟨htD, hcD⟩ := class_C (card_P_eq h) (hKc h).le C3D.misc C3D.diff.all C3D.sel.all
    C3D.comm.all
  have mC := Gen.andB_left C3C.misc
  have mD' := Gen.andB_left C3D.misc
  have hwC := allLt_spec (Gen.andB_left (Gen.andB_left mC))
  have hwD := allLt_spec (Gen.andB_left (Gen.andB_left mD'))
  obtain ⟨htC', hinv, hfix⟩ := outer_P (card_P_eq h) (hKc h).le thcDceData thcDce_chk hsh
    (by rw [thcDce_LT]; exact C3C.mu) hwC (by rw [thcDce_CB, thcDce_LT]; exact C3C.outer) nOut
    out_counts
  have hF := hfix _ hcC
  have hzC := conj_wit h hx hA hB hBi hk W3.w3C W3.d3C z hz
  have hzD := conj_wit h hx hA hB hBi hk W3.w3D W3.d3D z hz
  have hnc : ¬IsConj (⟨wval gen C3C.word, htC⟩ : K) ⟨wval gen C3D.word, htD⟩ := by
    intro hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    have e : (g : P) * wval gen C3C.word * (g : P)⁻¹ = wval gen C3D.word := congrArg Subtype.val hg
    have h1 := hinv g g.2 C3D.word hwD e
    rw [thcDce_LT] at h1
    have h2 := C3D.jv
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hsd : ∀ i j : Fin 2, i ≠ j →
      ¬IsConj (![⟨wval gen C3C.word, htC⟩, ⟨wval gen C3D.word, htD⟩] i : K)
        (![⟨wval gen C3C.word, htC⟩, ⟨wval gen C3D.word, htD⟩] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hnc
    · exact fun hc => hnc hc.symm
    · exact absurd rfl hij
  have key : Nat.card (Subgroup.centralizer ({z} : Set J)) *
      ∑ i : Fin 2, 634023936 / (![C3C.N1 * C3C.m1, C3D.N1 * C3D.m1] i) ≤
        (∑ D', fixB (C3C.N1 * C3C.m1) nOut D') * 634023936 :=
    card_centralizer_mul_le_of_conj (hKc h)
      ![⟨wval gen C3C.word, htC⟩, ⟨wval gen C3D.word, htD⟩] ![C3C.N1 * C3C.m1, C3D.N1 * C3D.m1]
      (fun i => by fin_cases i; exacts [hcC, hcD]) hsd 0 hF ψ hψ z
      (fun i => by fin_cases i; exacts [hzC, hzD])
  rw [show ∑ i : Fin 2, 634023936 / (![C3C.N1 * C3C.m1, C3D.N1 * C3D.m1] i) = 1956864 by
      decide +kernel,
    show ∑ D', fixB (C3C.N1 * C3C.m1) nOut D' = 540 by decide +kernel] at key
  omega

theorem card_centralizer_u_le :
    Nat.card (Subgroup.centralizer
      ({slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22} : Set J)) ≤ 174960 :=
  card_centralizer_z3C_le h _ mat_u

end CertificateChecks.KernelThCent

end
