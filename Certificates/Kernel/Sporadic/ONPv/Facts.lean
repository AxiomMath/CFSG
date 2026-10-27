module

public import Certificates.Kernel.Sporadic.ONPv.C502
public import Certificates.Kernel.Sporadic.ONPv.C503
public import Certificates.Kernel.Sporadic.ONPv.C505
public import Certificates.Kernel.Sporadic.ONPv.C506
public import Certificates.Kernel.ONSeven.Words
public import CFSG.Certificates.Kernel.Spor.ONPvSound
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.Words
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.FixCheck
public import CFSG.Sporadic.Schreier.ONThreePoint
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPv

open CFSG.KS.ONPv CFSG.KS.ONNQ CFSG.ONSchreier CFSG.LocalAnalysis.RankThreeTheoremC.ONPair
open CFSG.RankThree.Native CFSG.ClassicalInvolution.Phan.Q3G

theorem wv_codeLetters {n : Nat} (g : Nat → Equiv.Perm (Fin n)) (r : List (Fin 4 × Bool)) :
    wv g (codeLetters r) = wordVal (fun i : Fin 4 => g i.val) r := by
  induction r with
  | nil => simp [wv, codeLetters, wordVal]
  | cons l r ih =>
    obtain ⟨i, b⟩ := l
    simp only [codeLetters, List.map_cons] at ih ⊢
    rw [wv_cons, ih]
    cases b
    · have h1 : ¬ (0 : Int) < -((i.val : Int) + 1) := by omega
      have h2 : (-(-((i.val : Int) + 1))).toNat - 1 = i.val := by omega
      simp [lv, h1, h2, wordVal, letterVal]
    · have h1 : (0 : Int) < (i.val : Int) + 1 := by omega
      have h2 : ((i.val : Int) + 1).toNat - 1 = i.val := by omega
      simp [lv, h1, h2, wordVal, letterVal]

theorem evalWord_eq_wv {n m : Nat} (g : Nat → Equiv.Perm (Fin n)) :
    ∀ {w : List Int}, Lm m w →
      Quiver.SchreierGraph.evalWord (fun h : Fin m => g h) (ptoLetters m w) = wv g w
  | [], _ => by simp [ptoLetters, wv, Quiver.SchreierGraph.evalWord_nil]
  | z :: w, hw => by
    obtain ⟨⟨h0, hm⟩, hw'⟩ := Lm_cons hw
    have hcons : ptoLetters m (z :: w) =
        (⟨z.natAbs - 1, by omega⟩, decide (0 < z)) :: ptoLetters m w := by
      simp [ptoLetters, h0, hm]
    rw [hcons, wv_cons, ← evalWord_eq_wv g hw']
    by_cases hp : 0 < z
    · have e : z.natAbs - 1 = z.toNat - 1 := by omega
      simp only [hp, decide_true, Quiver.SchreierGraph.evalWord_cons_true, lv, ↓reduceIte, e]
    · have e : z.natAbs - 1 = (-z).toNat - 1 := by omega
      simp only [hp, decide_false, Quiver.SchreierGraph.evalWord_cons_false, lv, ↓reduceIte, e]

section Kit


theorem rp_on : Rp CertificateChecks.KernelSpor.ON.TT CertificateChecks.KernelSpor.ON.UU sgen 7 := by
  intro k hk x
  obtain ⟨a, b, -, -⟩ := CertificateChecks.KernelSpor.ONS.letters k hk x x.isLt
  obtain ⟨p1, p2⟩ := onSeven_prep_strong hk
  exact ⟨a.symm.trans (p1 x), b.symm.trans (p2 x)⟩

theorem sgen_mem7 : ∀ k < 7, sgen k ∈ Pv := fun k _ => sgen_mem k

theorem sep_pv : Sep Pv ⟨0, by decide⟩ ⟨227759, by decide⟩ ⟨100817, by decide⟩ :=
  fun _ ha _ hb e0 e1 e2 => eq_of_three ha hb e0 e1 e2

end Kit

theorem items_ok : ItemsOK OPV.D := by decide +kernel

section Facts


theorem pv502 : (∀ j < 29, wv (gI sgen OPV.D) (wd (OPV.D (178 + j))) = 1) ∧
    wv (gI sgen OPV.D) (wd (OPV.D 207)) = gI sgen OPV.D 79 ∧
    wv (gI sgen OPV.D) (wd (OPV.D 208)) = sgen 1 :=
  c502_sound rp_on items_ok sgen_mem7 sep_pv c502_b0 c502_b1 c502_b2

theorem pv502_hd : gI sgen OPV.D 79 ≠ 1 := c502Hd_sound rp_on items_ok c502_hd

theorem pv505 : ∀ j < 19, wv (qI sgen OPV.D) (wd (OPV.D (156 + j))) = 1 :=
  c505_sound rp_on items_ok sgen_mem7 sep_pv c505_b0 c505_b1 c505_b2

theorem pv505_hd : qI sgen OPV.D 0 ≠ 1 ∧
    ∀ k < 4, qI sgen OPV.D k ⟨0, by omega⟩ = ⟨0, by omega⟩ :=
  c505Hd_sound rp_on items_ok c505_hd

theorem pv503 : wv (fun k => qI sgen OPV.D (gsel k)) (wd (OPV.D 175)) = qI sgen OPV.D 3 ∧
    wv (fun k => qI sgen OPV.D (gsel k)) (wd (OPV.D 176)) =
      wv (fun k => qI sgen OPV.D (gsel k)) (wd (OPV.D 177)) :=
  c503_sound rp_on items_ok sgen_mem7 sep_pv c503_b0 c503_b1 c503_b2

theorem pv503_hd : qI sgen OPV.D 4 ⟨0, by omega⟩ ≠ ⟨0, by omega⟩ :=
  c503Hd_sound rp_on items_ok c503_hd

theorem pv506 :
    (∀ k < 2, qI sgen OPV.D (5 + k) * gI sgen OPV.D 92 * (qI sgen OPV.D (5 + k))⁻¹ =
      gI sgen OPV.D 92 ^ 3) ∧ ∀ m < 12, gI sgen OPV.D (80 + m) = gI sgen OPV.D (7 + m) :=
  c506_sound rp_on items_ok sgen_mem7 sep_pv c506_b0 c506_b1 c506_b2

theorem pv506_wit : ∀ j < 56, ∃ k < 2,
    ¬ Commute (qI sgen OPV.D (5 + k) * gI sgen OPV.D (93 + j) * (qI sgen OPV.D (5 + k))⁻¹)
      (gI sgen OPV.D (93 + j)) := by
  intro j hj
  rcases Nat.lt_or_ge j 28 with h | h
  · have := c506WitR_sound (lo := 0) (cnt := 28) rp_on items_ok c506_wit0 (by omega) j h
    rwa [Nat.zero_add] at this
  · have := c506WitR_sound (lo := 28) (cnt := 28) rp_on items_ok c506_wit1 (by omega) (j - 28)
      (by omega)
    rwa [show 28 + (j - 28) = j by omega] at this

end Facts

theorem items_main :
    wd (OPV.D 77) = h1Word ∧ wd (OPV.D 78) = h2Word ∧ wd (OPV.D 79) = alphaWordA ∧
      wd (OPV.D 153) = tWord ∧ wd (OPV.D 154) = n1Word ∧ wd (OPV.D 155) = n2Word ∧
      (List.range 18).map (fun j => wd (OPV.D (156 + j))) = sl3Rels7.map codeLetters ∧
      wd (OPV.D 174) = codeLetters (decodeWord 4 sl3OmegaCodes7) ∧ wd (OPV.D 175) = q4Word ∧
      wd (OPV.D 176) = [4, 1, 3, -1, -3, -4] ∧
      wd (OPV.D 177) = [1, 3, -1, -3, 1, 3, -1, -3, 1, 3, -1, -3, 1, 3, -1, -3] := by
  decide +kernel

theorem items_q : ∀ i < 4, wd (OPV.D (149 + i)) = qWords[i]! := by decide +kernel

theorem items_lines : ∀ j < 57, wd (OPV.D (92 + j)) = onSevenLineWords[j]! := by decide +kernel

theorem hwords_ok : Lm 7 h1Word ∧ Lm 7 h2Word ∧ (∀ i < 4, Lm 2 qWords[i]!) ∧ Lm 2 tWord ∧
    Lm 2 n1Word ∧ Lm 2 n2Word := by
  decide +kernel

section Hval


theorem hI_eq : ∀ k < 2, hI sgen OPV.D k = hgen k := by
  intro k hk
  have e0 : hI sgen OPV.D 0 = hgen 0 := by
    rw [hgen_zero, evalS, evalWord_eq_wv sgen hwords_ok.1, ← items_main.1]
    rfl
  have e1 : hI sgen OPV.D 1 = hgen 1 := by
    rw [hgen_one, evalS, evalWord_eq_wv sgen hwords_ok.2.1, ← items_main.2.1]
    rfl
  match k, hk with
  | 0, _ => exact e0
  | 1, _ => exact e1

theorem wv_hI {w : List Int} (hw : Lm 2 w) : wv (hI sgen OPV.D) w = hval w := by
  rw [hval, evalWord_eq_wv hgen hw]
  exact wv_congr hI_eq hw

theorem q_eq (i : Fin 4) : qI sgen OPV.D i.val = hval qWords[i.val]! := by
  unfold qI
  rw [items_q i.val i.isLt]
  exact wv_hI (hwords_ok.2.2.1 i.val i.isLt)

theorem t_eq : qI sgen OPV.D 4 = hval tWord := by
  unfold qI
  rw [show 149 + 4 = 153 from rfl, items_main.2.2.2.1]
  exact wv_hI hwords_ok.2.2.2.1

theorem n1_eq : qI sgen OPV.D 5 = hval n1Word := by
  unfold qI
  rw [show 149 + 5 = 154 from rfl, items_main.2.2.2.2.1]
  exact wv_hI hwords_ok.2.2.2.2.1

theorem n2_eq : qI sgen OPV.D 6 = hval n2Word := by
  unfold qI
  rw [show 149 + 6 = 155 from rfl, items_main.2.2.2.2.2.1]
  exact wv_hI hwords_ok.2.2.2.2.2

theorem qfun_eq : (fun i : Fin 4 => qI sgen OPV.D i.val) = fun i => hval qWords[i.val]! :=
  funext q_eq

theorem pv505_rels : ∀ r ∈ sl3Rels7, wordVal (fun i : Fin 4 => hval qWords[i.val]!) r = 1 := by
  intro r hr
  have hm : codeLetters r ∈ (List.range 18).map (fun j => wd (OPV.D (156 + j))) := by
    rw [items_main.2.2.2.2.2.2.1]
    exact List.mem_map_of_mem hr
  obtain ⟨j, hj, e⟩ := List.mem_map.1 hm
  have h := pv505 j (by have := List.mem_range.1 hj; omega)
  rw [e, wv_codeLetters, qfun_eq] at h
  exact h

theorem pv505_omega :
    wordVal (fun i : Fin 4 => hval qWords[i.val]!) (decodeWord 4 sl3OmegaCodes7) = 1 := by
  have h := pv505 18 (by omega)
  rw [show 156 + 18 = 174 from rfl, items_main.2.2.2.2.2.2.2.1, wv_codeLetters, qfun_eq] at h
  exact h

theorem pv505_ne : hval qWords[0]! ≠ 1 := fun e => pv505_hd.1 ((q_eq 0).trans e)

theorem pv505_fix (i : Fin 4) : hval qWords[i.val]! 0 = 0 := by
  rw [← q_eq i]
  exact pv505_hd.2 i.val i.isLt

theorem pv503_q4 : wv (fun k => qI sgen OPV.D (gsel k)) q4Word = hval qWords[3]! := by
  rw [← items_main.2.2.2.2.2.2.2.2.1, pv503.1]
  exact q_eq 3

theorem pv503_conj : wv (fun k => qI sgen OPV.D (gsel k)) [4, 1, 3, -1, -3, -4] =
    wv (fun k => qI sgen OPV.D (gsel k)) [1, 3, -1, -3, 1, 3, -1, -3, 1, 3, -1, -3, 1, 3, -1, -3] := by
  rw [← items_main.2.2.2.2.2.2.2.2.2.1, ← items_main.2.2.2.2.2.2.2.2.2.2]
  exact pv503.2

theorem pv503_move : hval tWord 0 ≠ 0 := by
  rw [← t_eq]
  exact pv503_hd

end Hval

end CertificateChecks.KernelSpor.ONPv

end
