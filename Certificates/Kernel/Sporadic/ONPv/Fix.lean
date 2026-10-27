module

public import Certificates.Kernel.Sporadic.ONPv.Facts
public import Certificates.Kernel.Sporadic.ONNQ.Final
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.LineTwo
public import CFSG.RankThree.Native.ONSevenDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPv

open CFSG.KS.ONPv CFSG.KS.ONNQ CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.LocalAnalysis.RankThreeTheoremC.ONPair CFSG.RankThree.Native

attribute [local irreducible] nqRho nqRhoA nqSig nqSigA nqAP nqL2 d0 d1 ONNQ.nqP
  CFSG.KS.SC.permF sgen evalS gI qI hval onSevenLine lineAct lineActA pvEval

theorem items_cent : ∀ m < 12, wd (OPV.D (80 + m)) = (onSevenCentWords[m / 4]!)[m % 4]! := by
  decide +kernel

theorem cent_size : ∀ r < 3, (onSevenCentWords[r]!).size = 4 := by decide +kernel

theorem items_two : (∀ m < 12, plettersOK 2 (wd (OPV.D (7 + m))) = true) ∧
    (∀ m < 12, Lm 2 (wd (OPV.D (7 + m)))) ∧ Lm 2 h1Word ∧ Lm 2 h2Word := by
  decide +kernel

theorem wv_two {n : Nat} (g : Nat → Equiv.Perm (Fin n)) {a b : Equiv.Perm (Fin n)} (h0 : g 0 = a)
    (h1 : g 1 = b) {w : List Int} (hw : Lm 2 w) : wv g w = nqEv2 a b w := by
  have e : ∀ k < 2, g k = (fun h : Nat => if h = 0 then a else b) k := by
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · simp [h0]
    · simp [h1]
  rw [wv_congr e hw, ← evalWord_eq_wv _ hw]
  rfl

theorem rp_line : Rp ONNQ.TT ONNQ.UU ONNQ.nqP 8 :=
  fun _ hk x => ⟨ONNQ.TT_eq hk x, ONNQ.UU_eq hk x⟩

section Lines


theorem act0 {w : List Int} (hw : Lm 2 w) : wv (fun h => ONNQ.nqP (twH 0 h)) w = nqRho w := by
  unfold nqRho
  refine wv_two _ ?_ ?_ hw
  · change ONNQ.nqP (twH 0 0) = d0
    rw [ONNQ.twH_vals.1, ONNQ.nqP_zero]
  · change ONNQ.nqP (twH 0 1) = d1
    rw [ONNQ.twH_vals.2.1, ONNQ.nqP_one]

theorem act1 {w : List Int} (hw : Lm 2 w) : wv (fun h => ONNQ.nqP (twH 1 h)) w = nqRhoA w := by
  unfold nqRhoA
  refine wv_two _ ?_ ?_ hw
  · change ONNQ.nqP (twH 1 0) = nqAP
    rw [ONNQ.twH_vals.2.2.2.2.1, ONNQ.nqP_five]
  · change ONNQ.nqP (twH 1 1) = d1
    rw [ONNQ.twH_vals.2.2.2.2.2.1, ONNQ.nqP_one]

theorem actN : wv (fun k => wv (fun h => ONNQ.nqP (twH 1 h)) (wd (OPV.D (77 + k))))
    (wd (OPV.D 154)) = nqSigA n1Word := by
  rw [items_main.2.2.2.2.1]
  unfold nqSigA
  refine wv_two _ ?_ ?_ hwords_ok.2.2.2.2.1
  · change wv (fun h => ONNQ.nqP (twH 1 h)) (wd (OPV.D 77)) = _
    rw [items_main.1, act1 items_two.2.2.1]
  · change wv (fun h => ONNQ.nqP (twH 1 h)) (wd (OPV.D 78)) = _
    rw [items_main.2.1, act1 items_two.2.2.2]

theorem l2_eq : (⟨58818, by omega⟩ : Fin 122760) = nqL2 := Fin.ext ONNQ.nqL2_val.symm

theorem ln506 :
    (∀ m < 8, wv (fun h => ONNQ.nqP (twH 0 h)) (wd (OPV.D (7 + m))) ⟨0, by omega⟩ = ⟨0, by omega⟩) ∧
      (∀ m < 4, wv (fun h => ONNQ.nqP (twH 1 h)) (wd (OPV.D (7 + m))) nqL2 = nqL2) ∧
      (∀ m < 4, wv (fun h => ONNQ.nqP (twH 1 h)) (wd (OPV.D (15 + m))) nqL2 = nqL2) ∧
      wv (fun k => wv (fun h => ONNQ.nqP (twH 1 h)) (wd (OPV.D (77 + k)))) (wd (OPV.D 154))
        nqL2 = nqL2 := by
  rw [← l2_eq]
  exact c506Ln_sound rp_line items_ok (l2 := ⟨58818, by omega⟩) c506_ln

theorem pvEval_u {m : Nat} (hm : m < 12) :
    pvEval ((onSevenCentWords[m / 4]!)[m % 4]!) = pvEval (wd (OPV.D (7 + m))) := by
  have h := pv506.2 m hm
  unfold gI at h
  apply Subtype.ext
  unfold pvEval
  dsimp only
  rw [← items_cent m hm, evalS, evalS, evalWord_eq_wv sgen (items_hi items_ok (80 + m)),
    evalWord_eq_wv sgen (items_lo items_ok (7 + m))]
  exact h

theorem cent_M1 {m : Nat} (hm : m < 8) : pvEval ((onSevenCentWords[m / 4]!)[m % 4]!) ∈ M1 := by
  rw [pvEval_u (by omega), mem_M1, lineAct_pvEval_nq (items_two.1 m (by omega)),
    ← act0 (items_two.2.1 m (by omega))]
  have h := ln506.1 m hm
  have e0 : (⟨0, by omega⟩ : Fin 122760) = 0 := rfl
  rw [e0] at h
  exact h


theorem lineActA_u {m : Nat} (hm : m < 12) :
    lineActA (pvEval ((onSevenCentWords[m / 4]!)[m % 4]!)) lineTwo = lineTwo ↔
      wv (fun h => ONNQ.nqP (twH 1 h)) (wd (OPV.D (7 + m))) nqL2 = nqL2 := by
  rw [pvEval_u hm, lineActA_pvEval_nq (items_two.1 m hm), lineTwo_eq_nqL2,
    ← act1 (items_two.2.1 m hm)]

theorem cent_G2 {m : Nat} (hm : m < 12) (h : m < 4 ∨ 8 ≤ m) :
    pvEval ((onSevenCentWords[m / 4]!)[m % 4]!) ∈ G2 := by
  rw [mem_G2, lineActA_u hm]
  rcases h with h | h
  · exact ln506.2.1 m h
  · have := ln506.2.2.1 (m - 8) (by omega)
    rwa [show 15 + (m - 8) = 7 + m by omega] at this

theorem n1_G2 : (⟨hval n1Word, hval_mem _⟩ : Pv) ∈ G2 := by
  rw [mem_G2, lineActA_hval_nq, lineTwo_eq_nqL2, ← actN]
  exact ln506.2.2.2

theorem gI_line (j : Fin 57) : gI sgen OPV.D (92 + j) = onSevenLine j := by
  unfold onSevenLine evalS gI
  rw [← items_lines j j.isLt, evalWord_eq_wv sgen (items_hi items_ok (92 + j))]

theorem fix_facts : (⟨hval n1Word, hval_mem _⟩ : Pv) ∈ G2 ∧
    (∀ k < (onSevenCentWords[0]!).size, pvEval (onSevenCentWords[0]!)[k]! ∈ M1 ⊓ G2) ∧
    (∀ k < (onSevenCentWords[1]!).size, pvEval (onSevenCentWords[1]!)[k]! ∈ M1) ∧
    (∀ k < (onSevenCentWords[2]!).size, pvEval (onSevenCentWords[2]!)[k]! ∈ G2) ∧
    (∀ w ∈ [n1Word, n2Word], hval w * onSevenLine 0 * (hval w)⁻¹ = onSevenLine 0 ^ 3) ∧
    ∀ j : Fin 56,
      ¬ Commute (hval n1Word * onSevenLine j.succ * (hval n1Word)⁻¹) (onSevenLine j.succ) ∨
      ¬ Commute (hval n2Word * onSevenLine j.succ * (hval n2Word)⁻¹) (onSevenLine j.succ) := by
  have hg : ∀ r < 3, ∀ k < (onSevenCentWords[r]!).size,
      pvEval (onSevenCentWords[r]!)[k]! = pvEval ((onSevenCentWords[(4 * r + k) / 4]!)[(4 * r + k) % 4]!) := by
    intro r hr k hk
    rw [cent_size r hr] at hk
    rw [show (4 * r + k) / 4 = r by omega, show (4 * r + k) % 4 = k by omega]
  have hx0 : gI sgen OPV.D 92 = onSevenLine 0 := by
    have h := gI_line 0
    rwa [Fin.val_zero, Nat.add_zero] at h
  refine ⟨n1_G2, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, fun j => ?_⟩
  · have hk' := hk
    rw [cent_size 0 (by omega)] at hk'
    rw [hg 0 (by omega) k hk]
    exact ⟨cent_M1 (by omega), cent_G2 (by omega) (Or.inl (by omega))⟩
  · have hk' := hk
    rw [cent_size 1 (by omega)] at hk'
    rw [hg 1 (by omega) k hk]
    exact cent_M1 (by omega)
  · have hk' := hk
    rw [cent_size 2 (by omega)] at hk'
    rw [hg 2 (by omega) k hk]
    exact cent_G2 (by omega) (Or.inr (by omega))
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have h := pv506.1 0 (by omega)
      rw [show 5 + 0 = 5 from rfl, n1_eq, hx0] at h
      exact h
    · have h := pv506.1 1 (by omega)
      rw [show 5 + 1 = 6 from rfl, n2_eq, hx0] at h
      exact h
  · have hj : gI sgen OPV.D (93 + j) = onSevenLine j.succ := by
      rw [← gI_line j.succ, Fin.val_succ]
      congr 1
      omega
    obtain ⟨k, hk, h⟩ := pv506_wit j j.isLt
    rw [hj] at h
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · left
      rwa [show 5 + 0 = 5 from rfl, n1_eq] at h
    · right
      rwa [show 5 + 1 = 6 from rfl, n2_eq] at h

end Lines

end CertificateChecks.KernelSpor.ONPv

end
