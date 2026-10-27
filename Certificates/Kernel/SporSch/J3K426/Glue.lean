module

public import Certificates.Kernel.SporSch.J3K426.Checks
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Misc.RuInvCov
public import Certificates.Certificate12624Base

public section

namespace CertificateChecks.KernelSporSch.J3KT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PkPow
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.RankThree.PartTwo.KFacts.K426

theorem strictN_id (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem arr {k : Nat} (hk : k < 40) : j3tArr k = unpack 6156 13 (F k) := by
  rw [j3tArr, CertificateChecks.KernelSporSch.J3KT.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound all k hk

theorem pp {k : Nat} (hk : k < 40) : PP 6156 13 (F k) := by
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts (CFSG.KS.Raw.Orb.allN_iff.1 perm k hk)
  have hc : canonK 6156 13 (mask 13) (6156 * 13) (F k) = true := by
    unfold canonK
    simp only [bAnd_iff]
    exact ⟨szOK', Nat.beq_eq.mpr h1,
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩
  refine ⟨hc, ⟨fun i hi => (h3 i hi).1, fun a ha b hb e => ?_⟩⟩
  rw [← (h3 a ha).2, ← (h3 b hb).2, e]

theorem fw_eq {m : Nat} (hm : m < 27) : E27 m = FW m :=
  (Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 eW m hm)).symm

theorem hX0 : j3tReps[0]! = unpack 6156 13 X0 := by
  rw [j3tReps, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
  exact arr (by norm_num)

theorem hX1 : j3tReps[1]! = unpack 6156 13 X1 := by
  rw [j3tReps, getElem!_pos _ 1 (by simp), Array.getElem_ofFn]
  exact arr (by norm_num)

theorem hD {l : Nat} (hl : l < 2) : j3tDGens[l]! = unpack 6156 13 (D l) := by
  rw [j3tDGens, getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  exact arr (by omega)

theorem hG : j3tG = unpack 6156 13 G := arr (by norm_num)

theorem hL {j : Nat} (hj : j < 13) : j3tLines[j]! = unpack 6156 13 (L j) := by
  rw [j3tLines, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact arr (by omega)

theorem ppX0 : PP 6156 13 X0 := pp (by norm_num)

theorem ppX1 : PP 6156 13 X1 := pp (by norm_num)

theorem ppD {l : Nat} (hl : l < 2) : PP 6156 13 (D l) := pp (by omega)

theorem ppG : PP 6156 13 G := pp (by norm_num)

theorem ppL {j : Nat} (hj : j < 13) : PP 6156 13 (L j) := pp (by omega)

theorem pow_eq {p : Nat} (hp : PP 6156 13 p) : ∀ e : Nat,
    powArr 6156 (unpack 6156 13 p) e = unpack 6156 13 (ppw 6156 13 p e) ∧
      PP 6156 13 (ppw 6156 13 p e)
  | 0 => ⟨idA_eq szOK', PP.id szOK'⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := pow_eq hp e
    have e1 : ppw 6156 13 p (e + 1) = pcomp 6156 13 (mask 13) p (ppw 6156 13 p e) :=
      strictN_id (ppw 6156 13 p e) (fun q => pcomp 6156 13 (mask 13) p q)
    rw [e1]
    exact ⟨by rw [powArr, h1, compA_PP hp h2], PP.mul hp h2⟩

theorem wv_eq {Gs : Nat → Nat} {gs : Array (Array Nat)}
    (hg : ∀ i < 2, gs[i]! = unpack 6156 13 (Gs i) ∧ PP 6156 13 (Gs i)) :
    ∀ W : List (Fin 2 × Bool),
      evalWA 6156 gs W = unpack 6156 13 (wv 6156 13 Gs (fun i => pinvS 6156 13 (mask 13) (Gs i)) W) ∧
        PP 6156 13 (wv 6156 13 Gs (fun i => pinvS 6156 13 (mask 13) (Gs i)) W)
  | [] => ⟨idA_eq szOK', PP.id szOK'⟩
  | x :: W => by
    obtain ⟨ih1, ih2⟩ := wv_eq hg W
    obtain ⟨hgx, hpx⟩ := hg x.1.val x.1.2
    have e1 : wv 6156 13 Gs (fun i => pinvS 6156 13 (mask 13) (Gs i)) (x :: W) =
        pcomp 6156 13 (mask 13) (Bool.rec (motive := fun _ => Nat)
          (pinvS 6156 13 (mask 13) (Gs x.1.val)) (Gs x.1.val) x.2)
          (wv 6156 13 Gs (fun i => pinvS 6156 13 (mask 13) (Gs i)) W) :=
      strictN_id _ _
    rw [evalWA, e1, ih1]
    rcases x with ⟨i, b⟩
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [hgx, invCand_PP hpx, compA_PP hpx.inv ih2]
      exact ⟨rfl, hpx.inv.mul ih2⟩
    · simp only [if_true]
      rw [hgx, compA_PP hpx ih2]
      exact ⟨rfl, hpx.mul ih2⟩

theorem countP_fix (n w p : Nat) :
    ((List.range n).countP fun x => (unpack n w p)[x]! == x) = nfix n w p := by
  unfold nfix
  rw [CFSG.KC.Misc.RuInv.P.foldN_count, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro x hx
  rw [unpack_getElem!, if_pos (List.mem_range.1 hx), Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem fix_eq (p : Nat) : Certificates.j3fix (unpack 6156 13 p) = nfix 6156 13 p :=
  countP_fix 6156 13 p

theorem not_of_bIf {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h Bool.false_ne_true

theorem or_of_bIf {c d : Bool} (h : bIf(c, true, d) = true) : c = true ∨ d = true := by
  cases c
  · exact Or.inr h
  · exact Or.inl rfl

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
open Certificates in
theorem facts12622 :
    eqA 6156 (compA 6156 j3tG j3tReps[0]!) (compA 6156 (compA 6156 j3tReps[0]! j3tReps[0]!) j3tG) =
        true ∧
      eqA 6156 (compA 6156 (compA 6156 j3tG j3tDGens[0]!) (compA 6156 j3tG j3tDGens[0]!))
        (idA 6156) = true := by
  refine ⟨?_, ?_⟩
  · rw [hG, hX0, compA_PP ppG ppX0, compA_PP ppX0 ppX0, compA_PP (ppX0.mul ppX0) ppG,
      eqA_PP (ppG.mul ppX0) ((ppX0.mul ppX0).mul ppG)]
    exact inv1
  · rw [hG, hD (by norm_num), compA_PP ppG (ppD (by norm_num)),
      compA_PP (ppG.mul (ppD (by norm_num))) (ppG.mul (ppD (by norm_num))), idA_eq szOK',
      eqA_PP ((ppG.mul (ppD (by norm_num))).mul (ppG.mul (ppD (by norm_num)))) (PP.id szOK')]
    exact inv2

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
open Certificates in
theorem facts12638 : allLt 2 (fun l => eqA 6156 (compA 6156 j3tReps[0]! j3tDGens[l]!)
    (compA 6156 j3tDGens[l]! j3tReps[0]!)) = true := by
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro l hl
  rw [hX0, hD hl, compA_PP ppX0 (ppD hl), compA_PP (ppD hl) ppX0,
    eqA_PP (ppX0.mul (ppD hl)) ((ppD hl).mul ppX0)]
  exact CFSG.KS.Raw.Orb.allN_iff.1 comm l hl

theorem hDg : ∀ i < 2, j3tDGens[i]! = unpack 6156 13 (D i) ∧ PP 6156 13 (D i) :=
  fun _ hi => ⟨hD hi, ppD hi⟩

theorem hU : evalWA 6156 j3tDGens j3tWu = unpack 6156 13 U ∧ PP 6156 13 U := wv_eq hDg j3tWu

theorem hV : evalWA 6156 j3tDGens j3tWv = unpack 6156 13 V ∧ PP 6156 13 V := wv_eq hDg j3tWv

theorem uv_eq (m : Nat) : Certificates.j3uvElt m = unpack 6156 13 (UV m) ∧ PP 6156 13 (UV m) := by
  unfold Certificates.j3uvElt
  rw [hU.1, hV.1, (pow_eq hU.2 _).1, (pow_eq hV.2 _).1, compA_PP (pow_eq hU.2 _).2 (pow_eq hV.2 _).2]
  exact ⟨rfl, (pow_eq hU.2 _).2.mul (pow_eq hV.2 _).2⟩

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
open Certificates in
theorem facts12624 :
    eqA 6156 (powArr 6156 (evalWA 6156 j3tDGens j3tWu) 3) (idA 6156) = true ∧
      eqA 6156 (powArr 6156 (evalWA 6156 j3tDGens j3tWv) 3) (idA 6156) = true ∧
      (List.range 9).all (fun m => (List.range m).all fun m' =>
        !eqA 6156 (j3uvElt m) (j3uvElt m')) = true ∧
      (List.range 9).all (fun m => decide (m = 0) || decide (j3fix (j3uvElt m) = 0)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hU.1, (pow_eq hU.2 3).1, idA_eq szOK', eqA_PP (pow_eq hU.2 3).2 (PP.id szOK')]
    exact u3
  · rw [hV.1, (pow_eq hV.2 3).1, idA_eq szOK', eqA_PP (pow_eq hV.2 3).2 (PP.id szOK')]
    exact v3
  · rw [List.all_eq_true]
    intro m hm
    rw [List.all_eq_true]
    intro m' hm'
    have hm9 := List.mem_range.1 hm
    have hmm := List.mem_range.1 hm'
    rw [(uv_eq m).1, (uv_eq m').1, eqA_PP (uv_eq m).2 (uv_eq m').2,
      not_of_bIf (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 uvDist m hm9) m' hmm)]
    rfl
  · rw [List.all_eq_true]
    intro m hm
    rcases or_of_bIf (CFSG.KS.Raw.Orb.allN_iff.1 uvFix m (List.mem_range.1 hm)) with h | h
    · rw [Nat.eq_of_beq_eq_true h]
      rfl
    · rw [(uv_eq m).1, fix_eq, Nat.eq_of_beq_eq_true h]
      simp

theorem e27_eq (m : Nat) : Certificates.j3e27Elt m = unpack 6156 13 (E27 m) ∧
    PP 6156 13 (E27 m) := by
  have h2 := pow_eq (ppL (j := 2) (by norm_num))
  have h4 := pow_eq (ppL (j := 4) (by norm_num))
  have h0 := pow_eq (ppL (j := 0) (by norm_num))
  unfold Certificates.j3e27Elt
  rw [hL (by norm_num), hL (by norm_num), hL (by norm_num), (h2 _).1, (h4 _).1, (h0 _).1,
    compA_PP (h2 _).2 (h4 _).2, compA_PP ((h2 _).2.mul (h4 _).2) (h0 _).2]
  exact ⟨rfl, ((h2 _).2.mul (h4 _).2).mul (h0 _).2⟩

theorem lines_comm {a b : Nat} (ha : a < 13) (hb : b < 13)
    (h : Nat.beq (pcomp 6156 13 (mask 13) (L a) (L b)) (pcomp 6156 13 (mask 13) (L b) (L a)) =
      true) :
    eqA 6156 (compA 6156 j3tLines[a]! j3tLines[b]!) (compA 6156 j3tLines[b]! j3tLines[a]!) =
      true := by
  rw [hL ha, hL hb, compA_PP (ppL ha) (ppL hb), compA_PP (ppL hb) (ppL ha),
    eqA_PP ((ppL ha).mul (ppL hb)) ((ppL hb).mul (ppL ha))]
  exact h

theorem facts12623a :
    eqA 6156 (compA 6156 j3tLines[2]! j3tLines[4]!) (compA 6156 j3tLines[4]! j3tLines[2]!) = true ∧
      eqA 6156 (compA 6156 j3tLines[2]! j3tLines[0]!) (compA 6156 j3tLines[0]! j3tLines[2]!) =
        true ∧
      eqA 6156 (compA 6156 j3tLines[4]! j3tLines[0]!) (compA 6156 j3tLines[0]! j3tLines[4]!) =
        true ∧
      (List.range 27).all (fun m => decide (m = 0) ||
        decide (Certificates.j3fix (Certificates.j3e27Elt m) = if m % 3 = 0 then 0 else 36)) =
          true ∧
      (List.range 27).all (fun m => (List.range m).all fun m' =>
        !eqA 6156 (Certificates.j3e27Elt m) (Certificates.j3e27Elt m')) = true ∧
      decide (Certificates.j3fix j3tReps[0]! = 36) = true ∧
      decide (Certificates.j3fix j3tReps[1]! = 0) = true := by
  have r0 : Nat.beq (nfix 6156 13 X0) 36 = true := by
    cases h : Nat.beq (nfix 6156 13 X0) 36
    · have h' := rFix
      rw [h] at h'
      exact absurd h' Bool.false_ne_true
    · rfl
  have r1 : Nat.beq (nfix 6156 13 X1) 0 = true := by
    have h' := rFix
    rw [r0] at h'
    exact h'
  refine ⟨lines_comm (by norm_num) (by norm_num) lc1, lines_comm (by norm_num) (by norm_num) lc2,
    lines_comm (by norm_num) (by norm_num) lc3, ?_, ?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro m hm
    rcases or_of_bIf (CFSG.KS.Raw.Orb.allN_iff.1 eFix m (List.mem_range.1 hm)) with h | h
    · rw [Nat.eq_of_beq_eq_true h]
      rfl
    · rw [(e27_eq m).1, fix_eq, fw_eq (List.mem_range.1 hm), Nat.eq_of_beq_eq_true h]
      rcases Nat.lt_or_ge 0 (m % 3) with h3 | h3
      · have hb : Nat.beq (m % 3) 0 = false := by
          rw [Bool.eq_false_iff]
          intro e
          exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
        rw [hb]
        simp [show m % 3 ≠ 0 by omega]
      · have h0 : m % 3 = 0 := by omega
        rw [h0]
        simp
  · rw [List.all_eq_true]
    intro m hm
    rw [List.all_eq_true]
    intro m' hm'
    have h27 : m' < 27 := (List.mem_range.1 hm').trans (List.mem_range.1 hm)
    rw [(e27_eq m).1, (e27_eq m').1, eqA_PP (e27_eq m).2 (e27_eq m').2,
      fw_eq (List.mem_range.1 hm), fw_eq h27, not_of_bIf (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 eDist m
        (List.mem_range.1 hm)) m' (List.mem_range.1 hm'))]
    rfl
  · rw [hX0, fix_eq, Nat.eq_of_beq_eq_true r0]
    rfl
  · rw [hX1, fix_eq, Nat.eq_of_beq_eq_true r1]
    rfl

end CertificateChecks.KernelSporSch.J3KT

end
