module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDense.Basic
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.E11.MonoEChk
public import CFSG.Certificates.Kernel.KDenseP.E11.C16955
import Certificates.Kernel.KDenseP.MonoTabL

public section

namespace CertificateChecks.KernelKDenseP.E11

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.E11
  CFSG.KC.KDenseP.TwoPoint
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.TwoPoint
  CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.E11M.MT = true := by
  kd_monoTabL CFSG.KD.E11ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.E11M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

@[expose] def tpWKb (e n : ℕ) : List (ℕ × ℕ) :=
  List.replicate e (0, 0) ++ List.replicate e (1, 0) ++ List.replicate e (2, 0) ++ List.replicate n (1, 1)

theorem tpWKb_getD_eq {e n x j : ℕ} (hx : x < 3) (hj : j < e) :
    (tpWKb e n).getD (e * x + j) (0, 0) = (x, 0) := by
  unfold tpWKb
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

theorem tpWKb_getD_ne {e n j : ℕ} (hj : j < n) : (tpWKb e n).getD (e * 3 + j) (0, 0) = (1, 1) := by
  unfold tpWKb
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_replicate]
  rw [show e * 3 + j - (e + e + e) = j by omega]
  simp [hj]

theorem tpWKb_length (e n : ℕ) : (tpWKb e n).length = 3 * e + n := by
  simp [tpWKb]
  omega

theorem wit_one : KernelKDense.wit 1 = bV () := by
  simp [KernelKDense.wit]

theorem tp3Bb_sound
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (eqs nes : List (List Native.Gen × List Native.Gen)) (hL : pairsLetterOK (tp3 eqs nes) = true)
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) {CH : ℕ → ℕ} {nch : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT (Y443.words (tp3 eqs nes)) S (CH k) = true)
    (hplan : planOKP (Y443.words (tp3 eqs nes)) CH nch IT = true)
    (hwk : wkOK IT (tpWKb eqs.length nes.length) = true) :
    agreeAll eqs = true ∧ ∀ e ∈ nes, (∀ g ∈ e.1, g.validB = true) ∧ (∀ g ∈ e.2, g.validB = true) ∧
      EdgeNoncomm.moveCheckAux (Native.evalWord e.1 (bV ())) (Native.evalWord e.2 (bV ())) = true := by
  obtain ⟨hl, hk⟩ := wkOK_spec hwk
  rw [tpWKb_length] at hl
  have it := itemL hd hL hS hc hplan
  refine ⟨List.all_eq_true.2 fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have hagree : wordLin eqs[j].1 = wordLin eqs[j].2 := by
      apply KernelKDense.Y443.eq_of_three
      intro x hx
      have ht : eqs.length * x + j < IT.length := by rw [hl]; nlinarith
      obtain ⟨k1, k2⟩ := hk _ ht
      rw [tpWKb_getD_eq hx hj] at k1 k2
      obtain ⟨v1, v2, c, -⟩ := it _ ht
      rw [tp3_getD_eq eqs nes hx hj] at v1 v2 c
      rw [k1] at c
      exact ⟨v1, v2, c k2⟩
    have ht : eqs.length * 0 + j < IT.length := by rw [hl]; omega
    obtain ⟨v1, v2, -, -⟩ := it _ ht
    rw [tp3_getD_eq eqs nes (by norm_num) hj] at v1 v2
    exact KernelKDenseP.agree_of_wordLin v1 v2 hagree
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have ht : eqs.length * 3 + j < IT.length := by rw [hl]; omega
    obtain ⟨k1, k2⟩ := hk _ ht
    rw [tpWKb_getD_ne hj] at k1 k2
    obtain ⟨v1, v2, -, n⟩ := it _ ht
    rw [tp3_getD_ne eqs nes hj] at v1 v2 n
    obtain ⟨k, hk', hne⟩ := n k2
    rw [k1, wit_one] at hne
    exact ⟨v1, v2, KernelKDenseP.moveCheckAux_of_res5 hk' hne⟩

open Lean in
macro "kd_e11% " pre:ident eqs:term:max nes:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(tp3Bb_sound CertificateChecks.KernelKDenseP.E11.data_ok $eqs $nes (by quickRfl)
      (S := $(n "S")) (fun x hx => by interval_cases x <;> rfl) (CH := $(n "CH"))
      (nch := kd_count% $pre $(mkIdent `t)) (IT := $(n "IT")) (by kd_allE $pre $(mkIdent `t))
      (by quickRfl) (by quickRfl))

theorem moveCheck_of_sepB {w : List Native.Gen}
    (h : (∀ g ∈ w, g.validB = true) ∧ (∀ g ∈ ([] : List Native.Gen), g.validB = true) ∧
      EdgeNoncomm.moveCheckAux (Native.evalWord w (bV ())) (Native.evalWord [] (bV ())) = true) :
    EdgeNoncomm.moveCheck w (bV ()) = true := by
  unfold EdgeNoncomm.moveCheck
  rw [Bool.and_eq_true]
  exact ⟨List.all_eq_true.2 h.1, h.2.2⟩

theorem c16955 : elevenDataCheck () = true := by
  obtain ⟨he, hn⟩ := kd_e11% CFSG.KD.E11.c16955 elevenPairs n16955
  unfold elevenDataCheck movesSome
  rw [he, moveCheck_of_sepB (hn (w0W, []) (by simp [n16955])),
    moveCheck_of_sepB (hn (commW, []) (by simp [n16955]))]
  simp only [Bool.or_true, Bool.true_or, Bool.and_self]

end CertificateChecks.KernelKDenseP.E11

end
