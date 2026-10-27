
module

public import Certificates.Kernel.KDenseP.Axis.Base
public import Certificates.Kernel.KDense.Basic
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Pairs
public import CFSG.Monster.AxisCount.CoverLetters
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionHom
public import CFSG.Monster.Existence.ELevelBasic
public import CFSG.Monster.Existence.TwoPoint.Fi23ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23MiscBase
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels0Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels1Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels2Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels3Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels4Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels5Base
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongADBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongMBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongPBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CommBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CubeBase
public import CFSG.Monster.Existence.TwoPoint.GammaExclCheckBase
public import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Co1Base

@[expose] public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster
  CFSG.Monster.AxisCount CFSG.Monster.B.Short CFSG.Monster.Griess

theorem resPN_four (S x p : ℕ) : (resPN 4 S x p : ZMod (2 ^ 4 - 1)) = (resP S x p : ZMod 15) := by
  unfold resPN resP
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  congr 1
  ring

theorem resN_four (v : Native.DVec) (k : ℕ) : (resN 4 v k : ZMod (2 ^ 4 - 1)) = (res15 v k : ZMod 15) := by
  unfold resN res15
  norm_num

theorem repN_four {v : Native.DVec} {s : St} (h : Rep v s) : RepN 4 v s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨fun q hq => ?_, fun p hp hq => ?_, h3, fun i hi j hj => ?_, fun p hp hq => ?_, h6,
    fun r hr j hj => ?_, fun p hp hq => ?_, h9⟩
  · rw [resPN_four, resN_four]
    exact h1 q hq
  · rw [resPN_four]
    exact h2 p hp hq
  · rw [resPN_four, resN_four]
    exact h4 i hi j hj
  · rw [resPN_four]
    exact h5 p hp hq
  · rw [resPN_four, resN_four]
    exact h7 r hr j hj
  · rw [resPN_four]
    exact h8 p hp hq

theorem five_dvd : 5 ∣ 2 ^ 4 - 1 := by norm_num

theorem res5_eq (v : Native.DVec) (k : ℕ) :
    DVec.res5 v k = ZMod.castHom five_dvd (ZMod 5) (resN 4 v k) := by
  have h1 : (2 : ZMod 5) ^ (4 - 1) = 3 := by decide
  simp only [resN, DVec.res5, map_mul, map_pow, map_intCast, map_ofNat, h1]

@[expose] def wkOK : List ℕ → List (ℕ × ℕ) → Bool
  | [], [] => true
  | it :: IT, w :: ws => (Nat.beq (it % 4) w.1 && Nat.beq (it / 4 % 2) w.2) && wkOK IT ws
  | _, _ => false

theorem wkOK_spec : ∀ {IT : List ℕ} {ws : List (ℕ × ℕ)}, wkOK IT ws = true →
    IT.length = ws.length ∧
      ∀ t < IT.length, IT[t]! % 4 = (ws.getD t (0, 0)).1 ∧ IT[t]! / 4 % 2 = (ws.getD t (0, 0)).2
  | [], [], _ => ⟨rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | it :: IT, w :: ws, h => by
    simp only [wkOK, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨l, hl⟩ := wkOK_spec h3
    refine ⟨by simp [l], fun t ht => ?_⟩
    rcases t with _ | t
    · simp [h1, h2]
    · have := hl t (by simpa using ht)
      simpa using this

@[expose] def tpWK (e n : ℕ) : List (ℕ × ℕ) :=
  List.replicate e (0, 0) ++ List.replicate e (1, 0) ++ List.replicate e (2, 0) ++ List.replicate n (0, 1)

theorem item5 {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    {p : List (List Native.Gen × List Native.Gen)}
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words p) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x)
    {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true) (hN : 2 * IT.length ≤ N)
    (t : ℕ) (ht : t < IT.length) :
    (∀ g ∈ (p.getD t ([], [])).1, g.validB = true) ∧ (∀ g ∈ (p.getD t ([], [])).2, g.validB = true) ∧
      (IT[t]! / 4 % 2 = 0 → Cong5D
        (Native.evalWord (p.getD t ([], [])).1 (KernelKDense.wit (IT[t]! % 4)))
        (Native.evalWord (p.getD t ([], [])).2 (KernelKDense.wit (IT[t]! % 4)))) ∧
      (IT[t]! / 4 % 2 = 1 → ∃ k < 196884,
        DVec.res5 (Native.evalWord (p.getD t ([], [])).1 (KernelKDense.wit (IT[t]! % 4))) k ≠
          DVec.res5 (Native.evalWord (p.getD t ([], [])).2 (KernelKDense.wit (IT[t]! % 4))) k) := by
  have hch : ∀ k < nIX, chunkOKN 4 2 5 F MT WL S (CHI k) = true := fun k hk' => by
    rw [hCHI]
    exact hc _ (hix k hk')
  have hinit : ∀ x < 3, RepN 4 (KernelKDense.wit x) (S x) := fun x hx =>
    repN_four (KernelKDense.rep_wit hS x hx)
  have hL : ∀ σ, ∀ g ∈ WL σ, letterOK g = true := fun σ g hg => by
    rw [hWL] at hg
    exact KernelKDenseP.Axis.decW_letterOK _ g hg
  obtain ⟨vA, vB, he, hn⟩ := planP_sound (by norm_num) (by norm_num) five_dvd hd WL hL S
    KernelKDense.wit hinit CHI nIX IT hplan hch t ht
  have hW : ∀ σ < N, WL σ = Y443.words p σ := fun σ hσ =>
    (hWL σ).trans (KernelKDenseP.Axis.wordsEqB_spec hw σ hσ)
  have e1 : WL (2 * t) = (p.getD t ([], [])).1 := by
    rw [hW _ (by omega), KernelKDenseP.Axis.words_even]
  have e2 : WL (2 * t + 1) = (p.getD t ([], [])).2 := by
    rw [hW _ (by omega), KernelKDenseP.Axis.words_odd]
  rw [e1] at vA
  rw [e2] at vB
  rw [e1, e2] at he hn
  refine ⟨vA, vB, fun hk k hk' => ?_, fun hk => ?_⟩
  · rw [res5_eq, res5_eq, he hk k hk']
  · obtain ⟨k, hk', hne⟩ := hn hk
    exact ⟨k, hk', by rwa [res5_eq, res5_eq]⟩

theorem tp3_getD_eq (eqs nes : List (List Native.Gen × List Native.Gen)) {x j : ℕ} (hx : x < 3)
    (hj : j < eqs.length) : (tp3 eqs nes).getD (eqs.length * x + j) ([], []) = eqs[j] := by
  unfold tp3
  simp only [List.getD_eq_getElem?_getD]
  interval_cases x
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega)]
    simp [hj]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by simp)]
    simp [hj]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append]
    rw [show eqs.length * 2 + j - (eqs.length + eqs.length) = j by omega]
    simp [hj]

theorem tp3_getD_ne (eqs nes : List (List Native.Gen × List Native.Gen)) {j : ℕ}
    (hj : j < nes.length) : (tp3 eqs nes).getD (eqs.length * 3 + j) ([], []) = nes[j] := by
  unfold tp3
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append]
  rw [show eqs.length * 3 + j - (eqs.length + eqs.length + eqs.length) = j by omega]
  simp [hj]

theorem tpWK_getD_eq {e n x j : ℕ} (hx : x < 3) (hj : j < e) :
    (tpWK e n).getD (e * x + j) (0, 0) = (x, 0) := by
  unfold tpWK
  simp only [List.getD_eq_getElem?_getD]
  interval_cases x
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega)]
    simp [hj]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by simp)]
    simp only [List.length_replicate]
    rw [show e * 1 + j - e = j by omega]
    simp [hj]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_replicate]
    rw [show e * 2 + j - (e + e) = j by omega]
    simp [hj]

theorem tpWK_getD_ne {e n j : ℕ} (hj : j < n) : (tpWK e n).getD (e * 3 + j) (0, 0) = (0, 1) := by
  unfold tpWK
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_replicate]
  rw [show e * 3 + j - (e + e + e) = j by omega]
  simp [hj]

theorem tpWK_length (e n : ℕ) : (tpWK e n).length = 3 * e + n := by
  simp [tpWK]
  omega

theorem tp3_sound
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (eqs nes : List (List Native.Gen × List Native.Gen))
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words (tp3 eqs nes)) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x)
    {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true) (hN : 2 * IT.length ≤ N)
    (hwk : wkOK IT (tpWK eqs.length nes.length) = true) :
    (∀ e ∈ eqs, wordLin e.1 = wordLin e.2) ∧ ∀ e ∈ nes, wordLin e.1 ≠ wordLin e.2 := by
  obtain ⟨hl, hk⟩ := wkOK_spec hwk
  rw [tpWK_length] at hl
  have it := item5 hd hw hWL hS hCHI hc hix hplan hN
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    apply KernelKDense.Y443.eq_of_three
    intro x hx
    have ht : eqs.length * x + j < IT.length := by rw [hl]; nlinarith
    obtain ⟨k1, k2⟩ := hk _ ht
    rw [tpWK_getD_eq hx hj] at k1 k2
    obtain ⟨v1, v2, c, -⟩ := it _ ht
    rw [tp3_getD_eq eqs nes hx hj] at v1 v2 c
    rw [k1] at c
    exact ⟨v1, v2, c k2⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have ht : eqs.length * 3 + j < IT.length := by rw [hl]; omega
    obtain ⟨k1, k2⟩ := hk _ ht
    rw [tpWK_getD_ne hj] at k1 k2
    obtain ⟨v1, v2, -, n⟩ := it _ ht
    rw [tp3_getD_ne eqs nes hj] at v1 v2 n
    obtain ⟨k, hk', hne⟩ := n k2
    exact wordLin_ne_of_res5_ne v1 v2 hk' hne

theorem tp3_valid {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ}
    (hd : dataOKP F MT KT TH OCT DU1 = true) (eqs nes : List (List Native.Gen × List Native.Gen))
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words (tp3 eqs nes)) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x)
    {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true) (hN : 2 * IT.length ≤ N)
    (hwk : wkOK IT (tpWK eqs.length nes.length) = true) :
    ∀ e ∈ eqs, (∀ g ∈ e.1, g.validB = true) ∧ ∀ g ∈ e.2, g.validB = true := by
  obtain ⟨hl, -⟩ := wkOK_spec hwk
  rw [tpWK_length] at hl
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have ht : eqs.length * 0 + j < IT.length := by rw [hl]; omega
  obtain ⟨v1, v2, -, -⟩ := item5 hd hw hWL hS hCHI hc hix hplan hN _ ht
  rw [tp3_getD_eq eqs nes (by norm_num) hj] at v1 v2
  exact ⟨v1, v2⟩

theorem item5_cong {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    {p : List (List Native.Gen × List Native.Gen)}
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words p) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x)
    {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true) (hN : 2 * IT.length ≤ N)
    {ws : List (ℕ × ℕ)} (hwk : wkOK IT ws = true) (t : ℕ) (ht : t < ws.length)
    (hk0 : (ws.getD t (0, 0)).2 = 0) :
    (∀ g ∈ (p.getD t ([], [])).1, g.validB = true) ∧ (∀ g ∈ (p.getD t ([], [])).2, g.validB = true) ∧
      Cong5D (Native.evalWord (p.getD t ([], [])).1 (KernelKDense.wit (ws.getD t (0, 0)).1))
        (Native.evalWord (p.getD t ([], [])).2 (KernelKDense.wit (ws.getD t (0, 0)).1)) := by
  obtain ⟨hl, hk⟩ := wkOK_spec hwk
  have ht' : t < IT.length := by omega
  obtain ⟨k1, k2⟩ := hk t ht'
  obtain ⟨v1, v2, c, -⟩ := item5 hd hw hWL hS hCHI hc hix hplan hN t ht'
  rw [k1] at c
  exact ⟨v1, v2, c (k2.trans hk0)⟩

theorem axis_sound
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (p : List (List Native.Gen × List Native.Gen))
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words p) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ}
    {IT : List ℕ} (hc : ∀ k < nch, chunkOKN 4 2 5 F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true)
    (h0 : listInitOK 4 [(0, 1), (1, 1), (24, -1), (300, -2)] (S 0) = true)
    (h1 : listInitOK 4 [(0, 1), (1, 1), (24, -1), (300, 2)] (S 1) = true) (h2 : S 2 = S 0)
    (hN : 2 * IT.length ≤ N) (hwk : wkOK IT (List.replicate p.length (0, 1)) = true) :
    ∀ e ∈ p, wordLin e.1 aStar ≠ wordLin e.2 aStar := by
  obtain ⟨hl, hk⟩ := wkOK_spec hwk
  rw [List.length_replicate] at hl
  have hch : ∀ k < nIX, chunkOKN 4 2 5 F MT WL S (CHI k) = true := fun k hk' => by
    rw [hCHI]
    exact hc _ (hix k hk')
  have hinit := KernelKDenseP.Axis.rep_wit (by norm_num) h0 h1 h2
  have hL : ∀ σ, ∀ g ∈ WL σ, letterOK g = true := fun σ g hg => by
    rw [hWL] at hg
    exact KernelKDenseP.Axis.decW_letterOK _ g hg
  have hW : ∀ σ < N, WL σ = Y443.words p σ := fun σ hσ =>
    (hWL σ).trans (KernelKDenseP.Axis.wordsEqB_spec hw σ hσ)
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
  have ht' : t < IT.length := by omega
  obtain ⟨k1, k2⟩ := hk t ht'
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, ht, ite_true, Option.getD_some]
    at k1 k2
  obtain ⟨vA, vB, -, hn⟩ := planP_sound (by norm_num) (by norm_num) five_dvd hd WL hL S
    KernelKDenseP.Axis.wit hinit CHI nIX IT hplan hch t ht'
  have hg : p.getD t ([], []) = p[t] := by simp [List.getD_eq_getElem?_getD, ht]
  have e1 : WL (2 * t) = p[t].1 := by
    rw [hW _ (by omega), KernelKDenseP.Axis.words_even, hg]
  have e2 : WL (2 * t + 1) = p[t].2 := by
    rw [hW _ (by omega), KernelKDenseP.Axis.words_odd, hg]
  rw [e1, e2, k1] at hn
  rw [e1] at vA
  rw [e2] at vB
  obtain ⟨k, hk', hne⟩ := hn k2
  have h := wordLin_apply_ne_of_res5_ne vA vB hk' (by rwa [res5_eq, res5_eq])
  rwa [KernelKDenseP.Axis.interp_wit] at h

theorem ne_of_tauP {l : List (List Native.Gen × List Native.Gen)}
    (h : ∀ e ∈ tauP l, wordLin e.1 ≠ wordLin e.2) : ∀ e ∈ l, wordLin e.1 ≠ wordLin e.2 := by
  intro e he h'
  apply h (e.1 ++ [.tau], e.2 ++ [.tau]) (List.mem_map_of_mem he)
  rw [wordLin_append, wordLin_append, h']

theorem apply_ne_of_tauP {l : List (List Native.Gen × List Native.Gen)} {x : SpaceB}
    (h : ∀ e ∈ tauP l, wordLin e.1 x ≠ wordLin e.2 x) : ∀ e ∈ l, wordLin e.1 x ≠ wordLin e.2 x := by
  intro e he h'
  apply h (e.1 ++ [.tau], e.2 ++ [.tau]) (List.mem_map_of_mem he)
  rw [wordLin_append, wordLin_append, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h']

end CertificateChecks.KernelKDenseP.TwoPoint

end
