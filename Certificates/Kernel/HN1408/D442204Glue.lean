module

public import Certificates.Kernel.HN1408.D442204Chk
public import Certificates.Kernel.HN1408.CzTScan
public import Certificates.Kernel.HN1408.Y442202Glue
public import Certificates.Kernel.HN1408.TableIShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5DDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5LetterSpec
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Enum

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.D442204

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  CFSG.KS.RecGroup CFSG.KC.BfsPin CFSG.KD.HN1408 CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.KS.Raw.Orb (bAnd_eq)

#kc_forall_chunks cov_all (fun s => covS s = true) 20 CFSG.KD.HN1408.ch442204cov.sl 1

theorem lw_fold {X₁ X₂ X₃ : Nat} {subs : List (List Nat)} :
    ∀ (l : List Nat) {acc : Nat} {g : Equiv.Perm (Fin 1408)}, RepC acc g →
      (∀ i ∈ l, RepC (sub3 X₁ X₂ X₃ i) (elemW (subs.getD (i - 1) []))) →
      RepC (l.foldl (fun acc i => pc acc (sub3 X₁ X₂ X₃ i)) acc) (g * elemW (expandL subs l))
  | [], _, _, h, _ => by
    rw [expandL, List.flatMap_nil, elemW_nil_eq_one, mul_one]
    exact h
  | i :: l, _, _, h, hs => by
    rw [List.foldl_cons, expandL, List.flatMap_cons, elemW_append, ← mul_assoc]
    exact lw_fold l (repC_pc h (hs i (by simp))) fun j hj => hs j (by simp [hj])

theorem rc_lwK {X₁ X₂ X₃ : Nat} {subs : List (List Nat)} {l : List Nat}
    (hs : ∀ i ∈ l, RepC (sub3 X₁ X₂ X₃ i) (elemW (subs.getD (i - 1) []))) :
    RepC (lwK X₁ X₂ X₃ l) (elemW (expandL subs l)) := by
  have h := lw_fold l repC_idK hs
  rw [one_mul] at h
  exact h

theorem sub3_of {X₁ X₂ X₃ : Nat} {w₁ w₂ w₃ : List Nat} {subs : List (List Nat)}
    (e₁ : subs.getD 0 [] = w₁) (e₂ : subs.getD 1 [] = w₂) (e₃ : subs.getD 2 [] = w₃)
    (h₁ : RepC X₁ (elemW w₁)) (h₂ : RepC X₂ (elemW w₂)) (h₃ : RepC X₃ (elemW w₃))
    {l : List Nat} (hl : ∀ i ∈ l, i = 1 ∨ i = 2 ∨ i = 3) :
    ∀ i ∈ l, RepC (sub3 X₁ X₂ X₃ i) (elemW (subs.getD (i - 1) [])) := by
  intro i hi
  rcases hl i hi with rfl | rfl | rfl
  · change RepC X₁ (elemW (subs.getD 0 []))
    rw [e₁]
    exact h₁
  · change RepC X₂ (elemW (subs.getD 1 []))
    rw [e₂]
    exact h₂
  · change RepC X₃ (elemW (subs.getD 2 []))
    rw [e₃]
    exact h₃

theorem sub2_of {X₁ X₂ X₃ : Nat} {w₁ w₂ : List Nat} {subs : List (List Nat)}
    (e₁ : subs.getD 0 [] = w₁) (e₂ : subs.getD 1 [] = w₂)
    (h₁ : RepC X₁ (elemW w₁)) (h₂ : RepC X₂ (elemW w₂))
    {l : List Nat} (hl : ∀ i ∈ l, i = 1 ∨ i = 2) :
    ∀ i ∈ l, RepC (sub3 X₁ X₂ X₃ i) (elemW (subs.getD (i - 1) [])) := by
  intro i hi
  rcases hl i hi with rfl | rfl
  · change RepC X₁ (elemW (subs.getD 0 []))
    rw [e₁]
    exact h₁
  · change RepC X₂ (elemW (subs.getD 1 []))
    rw [e₂]
    exact h₂

theorem repC_pow {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (e : Nat) :
    RepC (ppK X e) (g ^ e) := by
  refine ⟨cn_ppK hX.1 e, ?_⟩
  rw [← powT_eq hX.1 e]
  exact Rep.powT (by norm_num) hX.2 e

theorem repC_of_rel {P X Q : Nat} {p q : Equiv.Perm (Fin 1408)} (hX : Cn X) (hP : RepC P p)
    (hQ : RepC Q q) (e : pc P X = Q) : RepC X (p⁻¹ * q) := by
  refine repC_of_pt hX fun x hx => ?_
  have hy : pt X x < 1408 := pt_lt hX hx
  have h1 : pt (pc P X) x = (p ⟨pt X x, hy⟩).val := by
    rw [pt_pc hP.1 hx, repC_pt hP hy]
  rw [e, repC_pt hQ hx] at h1
  have h3 : p ⟨pt X x, hy⟩ = q ⟨x, hx⟩ := Fin.ext h1.symm
  rw [Equiv.Perm.mul_apply, ← h3]
  simp

theorem pt_comp {D A B : Nat} {d c : Equiv.Perm (Fin 1408)} (hD : RepC D d)
    (hev : ∀ x (hx : x < 1408), pt A (pt B x) = (c ⟨x, hx⟩).val) {x : Nat} (hx : x < 1408) :
    pt D (pt A (pt B x)) = ((d * c) ⟨x, hx⟩).val := by
  have hy : pt A (pt B x) < 1408 := by
    rw [hev x hx]
    exact Fin.isLt _
  have e : (⟨pt A (pt B x), hy⟩ : Fin 1408) = c ⟨x, hx⟩ := Fin.ext (hev x hx)
  rw [repC_pt hD hy, Equiv.Perm.mul_apply, e]

theorem conjB_of {A B U V : Nat} {g u v : Equiv.Perm (Fin 1408)}
    (hev : ∀ x (hx : x < 1408), pt A (pt B x) = (g ⟨x, hx⟩).val) (hU : RepC U u) (hV : RepC V v)
    (hc : g * u = v * g) :
    conjB A B U V (pt A (pt B 0)) (pt A (pt B 1)) = true := by
  have e : ∀ x (hx : x < 1408), pt A (pt B (pt U x)) = pt V (pt A (pt B x)) := by
    intro x hx
    have hy : pt U x < 1408 := pt_lt hU.1 hx
    have hux : (⟨pt U x, hy⟩ : Fin 1408) = u ⟨x, hx⟩ := Fin.ext (repC_pt hU hx)
    have hgx : pt A (pt B x) < 1408 := by
      rw [hev x hx]
      exact Fin.isLt _
    have hfg : (⟨pt A (pt B x), hgx⟩ : Fin 1408) = g ⟨x, hx⟩ := Fin.ext (hev x hx)
    rw [hev _ hy, repC_pt hV hgx, hux, hfg]
    have := congrArg (fun k : Equiv.Perm (Fin 1408) => (k ⟨x, hx⟩).val) hc
    simpa only [Equiv.Perm.mul_apply] using this
  unfold conjB
  rw [e 0 (by norm_num), e 1 (by norm_num), Nat.beq_refl, Nat.beq_refl]

theorem bIf_or {a b : Bool} (h : a = true ∨ b = true) : bIf(a, true, b) = true := by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

theorem headK_parts {H : Nat → Nat} (h : headK H = true) :
    H 18 = lwK Y1 Y2 idK (uLetters.getD 0 []) ∧ H 19 = WK g0Word ∧
    pc (H 19) (pc (WK wordA) (WK wordZ)) = pc (H 18) (H 19) ∧
    Cn (H 0) ∧ pc (H 19) (H 0) = pc (pc (WK wordA) (WK wordZ)) (H 19) ∧
    Cn (H 1) ∧ pc (H 19) (H 1) = pc (pc (pc (WK wordA) (WK wordZ)) (H 18)) (H 19) ∧
    commP Y1 (WK wordZ) = true ∧ commP Y2 (WK wordZ) = true ∧
    ∀ j < 16, Cn (H (Nat.add 2 j)) ∧ pc (WK (gWords.getD j [])) (H (Nat.add 2 j)) = H 19 ∧
      commP (H (Nat.add 2 j)) (WK wordZ) = true := by
  unfold headK at h
  generalize WK wordZ = Z at h ⊢
  generalize WK wordA = A at h ⊢
  simp only [strictB_app] at h
  obtain ⟨h1, h⟩ := mkA h
  obtain ⟨h2, h⟩ := mkA h
  obtain ⟨h3, h⟩ := mkA h
  obtain ⟨h4, h⟩ := mkA h
  obtain ⟨h5, h⟩ := mkA h
  obtain ⟨h6, h⟩ := mkA h
  obtain ⟨h7, h⟩ := mkA h
  obtain ⟨h8, h⟩ := mkA h
  obtain ⟨h9, h⟩ := mkA h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, h4,
    Nat.eq_of_beq_eq_true h5, h6, Nat.eq_of_beq_eq_true h7, h8, h9, fun j hj => ?_⟩
  obtain ⟨a, b⟩ := mkA (allN_spec h j hj)
  obtain ⟨b, c⟩ := mkA b
  exact ⟨a, Nat.eq_of_beq_eq_true b, c⟩

theorem cellK_spec {H : Nat → Nat} {A B F : Nat} (h : cellK H A B F = true)
    (hc : bIf(conjB A B (H 18) (H 0) (pt A (pt B 0)) (pt A (pt B 1)), true,
      conjB A B (H 18) (H 1) (pt A (pt B 0)) (pt A (pt B 1))) = true) :
    704 ≤ pt (H 19) (pt A (pt B 0)) ∨ ∃ jj < 16, ∃ k < 240,
      isBase (pt (H (Nat.add 2 jj)) (pt A (pt B 0))) (pt (H (Nat.add 2 jj)) (pt A (pt B 1)))
        (pt (Y442202.Y0.T k) 0) (pt (Y442202.Y0.T k) 1) = true := by
  unfold cellK at h
  simp only [strictB_app] at h
  rcases mkIf h with ⟨-, h⟩ | ⟨hf, -⟩
  · rcases mkIf h with ⟨e, -⟩ | ⟨-, h⟩
    · exact Or.inl (Nat.le_of_ble_eq_true e)
    · rcases mkIf h with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h Bool.false_ne_true
      · obtain ⟨hjj, h⟩ := mkA h
        exact Or.inr ⟨Nat.div (Nat.pred F) 240, Nat.blt_eq.mp hjj, Nat.mod (Nat.pred F) 240,
          Nat.mod_lt _ (by norm_num), h⟩
  · rw [hc] at hf
    exact absurd hf (by decide)

theorem cell_at {i j : Nat} (hi : i < 1280) (hj : j < 24) :
    cellK H (T0 i) (T1 j) (fd (C i) j) = true := by
  have hs : i / 64 < 20 := by omega
  have h := cov_all (i / 64) hs
  unfold covS covSl at h
  have h' := allN_spec h (i % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h'
  simp only [strictB_app] at h'
  unfold rowK at h'
  exact allN_spec h' j hj

theorem kill_at {j : Nat} (hj : j < 16) (hne : j ≠ jStar) :
    ppK (lwK Y1 Y2 (WK (gWords.getD j [])) (killData.getD j ([], 0)).1)
      (Nat.div (killData.getD j ([], 0)).2 2) = WK wordA := by
  have h := allN_spec kill_ok j hj
  unfold killK at h
  have e0 : Nat.beq j jStar = false :=
    Bool.eq_false_iff.2 fun h' => hne (Nat.eq_of_beq_eq_true h')
  rw [e0] at h
  simp only [strictB_app] at h
  exact Nat.eq_of_beq_eq_true h

theorem fixK_parts {p : Nat} (h : fixK p = true) : p < 1408 ∧ pt Y1 p = p ∧ pt Y2 p = p ∧
    pt (WK (gWords.getD jStar [])) p = p := by
  unfold fixK at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, d⟩ := mkA h
  exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c,
    Nat.eq_of_beq_eq_true d⟩

theorem syl_gen {G : Nat → Nat} {i k : Nat} (h : sylGK G i k = true) {j : Nat} (hj : j < k) :
    G j = lwK Y1 Y2 (WK (gWords.getD jStar [])) ((sylowLetters.getD i []).getD j []) := by
  unfold sylGK at h
  simp only [strictB_app] at h
  exact Nat.eq_of_beq_eq_true (allN_spec h j hj)

theorem rec_card {G GI T PL POS SRT SRI : ℕ → ℕ} {k cnt : ℕ} {g : ℕ → Equiv.Perm (Fin 1408)}
    (hr : Y442202.recOK G GI k cnt T PL POS SRT SRI = true) (hg : ∀ j < k, RepC (G j) (g j)) :
    Nat.card ↥(closure (g '' {j | j < k})) = cnt := by
  unfold Y442202.recOK at hr
  rw [bAnd_eq, Bool.and_eq_true] at hr
  have hp : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) false G GI k cnt T PL POS SRT SRI i =
      true := fun i hi =>
    CFSG.KS.BaseMask.penumSl_spec hr.2 (Nat.zero_le i) (Nat.lt_of_lt_of_le hi (Nat.le_add_left _ _)) hi
  obtain ⟨x, -, -, -, -, hcard⟩ := penumLeft_closure (n := 1408) (w := 11) (k := k)
    (cnt := cnt) (cap := 4096) (g := g) hn (by norm_num) hg hr.1 hp
  exact hcard

theorem lett_g : ∀ j < 16, lettersOK (gWords.getD j []) = true := by decide

theorem kill_letters : ∀ j < 16, ∀ i ∈ (killData.getD j ([], 0)).1, i = 1 ∨ i = 2 ∨ i = 3 := by
  decide

theorem syl_letters :
    ∀ i < 3, ∀ j < 2, ∀ l ∈ (sylowLetters.getD i []).getD j [], l = 1 ∨ l = 2 ∨ l = 3 := by
  decide

theorem rc_g {j : Nat} (hj : j < 16) : RepC (WK (gWords.getD j [])) (elemW (gWords.getD j [])) :=
  repC_word (lett_g j hj)

theorem rc_y1 : RepC Y1 (elemW (yWord 0 0)) := by
  have e := Nat.eq_of_beq_eq_true (allN_spec Y442202.gens_parts.2.2.1 0 (by norm_num))
  unfold Y1
  rw [e]
  exact repC_word (by decide)

theorem rc_y2 : RepC Y2 (elemW (yWord 0 1)) := by
  have e := Nat.eq_of_beq_eq_true (allN_spec Y442202.gens_parts.2.2.1 1 (by norm_num))
  unfold Y2
  rw [e]
  exact repC_word (by decide)

@[expose] def gSubs (j : Nat) : List (List Nat) := [yWord 0 0, yWord 0 1, gWords.getD j []]

theorem gSubs_mem {j : Nat} {S : Subgroup (Equiv.Perm (Fin 1408))} (h1 : yOne 0 ∈ S)
    (h2 : yTwo 0 ∈ S) (h3 : gElt j ∈ S) : ∀ w ∈ gSubs j, elemW w ∈ S := by
  intro v hv
  simp only [gSubs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem syl_of {i k k' cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat} (hi : i < 3)
    (hk : k' ≤ 2) (hkk : k = k') (hG : sylGK G i k' = true)
    (hr : Y442202.recOK G GI k cnt T PL POS SRT SRI = true) :
    ∃ Q ≤ wGroup, Nat.card ↥Q = cnt := by
  subst hkk
  have hg : ∀ j < k, RepC (G j)
      (elemW (expandL (gSubs jStar) ((sylowLetters.getD i []).getD j []))) := by
    intro j hj
    rw [syl_gen hG hj]
    exact rc_lwK (sub3_of (subs := gSubs jStar) rfl rfl rfl rc_y1 rc_y2
      (rc_g (j := jStar) (by decide))
      (syl_letters i hi j (by omega)))
  refine ⟨_, ?_, rec_card hr hg⟩
  rw [closure_le]
  rintro _ ⟨j, -, rfl⟩
  refine elemW_expandL_mem (gSubs_mem ?_ ?_ ?_) _
  · exact subset_closure (by simp [yOne])
  · exact subset_closure (by simp [yTwo])
  · exact subset_closure (by simp [gElt])

theorem dFactsK (hP : Nat.card ↥P1408 = 177408000) : DFacts := by
  obtain ⟨hU, hG0, hGT, hc0, hr0, hc1, hr1, hy1z, hy2z, hD⟩ := headK_parts head_ok
  have hz : RepC (WK wordZ) elemZ := repC_word (by decide)
  have ha : RepC (WK wordA) elemA := repC_word (by decide)
  have hT : RepC (pc (WK wordA) (WK wordZ)) (elemA * elemZ) := repC_pc ha hz
  have rG0 : RepC (H 19) (elemW g0Word) := by
    rw [hG0]
    exact repC_word (by decide)
  have rU : RepC (H 18) (uElt 0) := by
    rw [hU]
    exact rc_lwK (subs := ykWords.getD 0 [])
      (sub2_of rfl rfl rc_y1 rc_y2 (by decide : ∀ i ∈ uLetters.getD 0 [], i = 1 ∨ i = 2))
  have rU1 : RepC (H 0) ((elemW g0Word)⁻¹ * ((elemA * elemZ) * elemW g0Word)) :=
    repC_of_rel hc0 rG0 (repC_pc hT rG0) hr0
  have rU2 : RepC (H 1) ((elemW g0Word)⁻¹ * (((elemA * elemZ) * uElt 0) * elemW g0Word)) :=
    repC_of_rel hc1 rG0 (repC_pc (repC_pc hT rU) rG0) hr1
  have rD : ∀ j < 16, RepC (H (Nat.add 2 j)) ((gElt j)⁻¹ * elemW g0Word) :=
    fun j hj => repC_of_rel (hD j hj).1 (rc_g hj) rG0 (hD j hj).2.1
  have htbl : elemW g0Word * (elemA * elemZ) = uElt 0 * elemW g0Word :=
    eq_of_repC (repC_pc rG0 hT) (by rw [hGT]; exact repC_pc rU rG0)
  have haC : ∀ g ∈ P1408, elemA * g = g * elemA := basic_ab.2.2.1
  have hY1C := mem_cent_of rc_y1 (elemW_mem _) hy1z
  have hY2C := mem_cent_of rc_y2 (elemW_mem _) hy2z
  have hdC : ∀ j < 16, (gElt j)⁻¹ * elemW g0Word ∈
      P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := fun j hj =>
    mem_cent_of (rD j hj) (P1408.mul_mem (P1408.inv_mem (elemW_mem _)) (elemW_mem _))
      (hD j hj).2.2
  have hY0le : yK 0 ≤ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
    rw [yK, wSub, closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have e : ykWords.getD 0 [] = [yWord 0 0, yWord 0 1] := rfl
    rw [Set.mem_setOf_eq, e] at hw
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hY1C
    · exact hY2C
  obtain ⟨xY, RY⟩ := Y442202.rY0
  have cover : ∀ h ∈ pPrime, h * (elemA * elemZ) * h⁻¹ = uElt 0 →
      (h * uElt 0 * h⁻¹ = elemA * elemZ ∨ h * uElt 0 * h⁻¹ = elemA * elemZ * uElt 0) →
        ∃ j < 16, (gElt j)⁻¹ * h ∈ yK 0 := by
    intro hh hp hconj hnorm
    rw [pPrime] at hp
    have hhP : hh ∈ P1408 := (mem_inf.mp hp).1
    have hhB : hh ∈ blocks1408 := (mem_inf.mp hp).2
    have hG0t : (elemW g0Word)⁻¹ * uElt 0 * elemW g0Word = elemA * elemZ := by
      calc (elemW g0Word)⁻¹ * uElt 0 * elemW g0Word
          = (elemW g0Word)⁻¹ * (uElt 0 * elemW g0Word) := by group
        _ = (elemW g0Word)⁻¹ * (elemW g0Word * (elemA * elemZ)) := by rw [← htbl]
        _ = elemA * elemZ := by group
    have hc_conj : ((elemW g0Word)⁻¹ * hh) * (elemA * elemZ) * ((elemW g0Word)⁻¹ * hh)⁻¹
        = elemA * elemZ := by
      calc ((elemW g0Word)⁻¹ * hh) * (elemA * elemZ) * ((elemW g0Word)⁻¹ * hh)⁻¹
          = (elemW g0Word)⁻¹ * (hh * (elemA * elemZ) * hh⁻¹) * elemW g0Word := by group
        _ = (elemW g0Word)⁻¹ * uElt 0 * elemW g0Word := by rw [hconj]
        _ = elemA * elemZ := hG0t
    have hcC : (elemW g0Word)⁻¹ * hh ∈
        P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
      rw [← cent_az haC]
      refine mem_inf.mpr ⟨P1408.mul_mem (P1408.inv_mem (elemW_mem g0Word)) hhP, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp hc_conj
    have hcu : ((elemW g0Word)⁻¹ * hh) * uElt 0
          = ((elemW g0Word)⁻¹ * ((elemA * elemZ) * elemW g0Word)) * ((elemW g0Word)⁻¹ * hh) ∨
        ((elemW g0Word)⁻¹ * hh) * uElt 0
          = ((elemW g0Word)⁻¹ * (((elemA * elemZ) * uElt 0) * elemW g0Word)) *
              ((elemW g0Word)⁻¹ * hh) := by
      rcases hnorm with hnorm | hnorm
      · left
        have hh' : hh * uElt 0 = (elemA * elemZ) * hh := mul_inv_eq_iff_eq_mul.mp hnorm
        calc ((elemW g0Word)⁻¹ * hh) * uElt 0
            = (elemW g0Word)⁻¹ * (hh * uElt 0) := by group
          _ = (elemW g0Word)⁻¹ * ((elemA * elemZ) * hh) := by rw [hh']
          _ = ((elemW g0Word)⁻¹ * ((elemA * elemZ) * elemW g0Word)) *
                ((elemW g0Word)⁻¹ * hh) := by group
      · right
        have hh' : hh * uElt 0 = (elemA * elemZ) * uElt 0 * hh := mul_inv_eq_iff_eq_mul.mp hnorm
        calc ((elemW g0Word)⁻¹ * hh) * uElt 0
            = (elemW g0Word)⁻¹ * (hh * uElt 0) := by group
          _ = (elemW g0Word)⁻¹ * (((elemA * elemZ) * uElt 0) * hh) := by rw [hh']
          _ = ((elemW g0Word)⁻¹ * (((elemA * elemZ) * uElt 0) * elemW g0Word)) *
                ((elemW g0Word)⁻¹ * hh) := by group
    have hB : elemW g0Word * ((elemW g0Word)⁻¹ * hh) ∈ blocks1408 := by
      rw [mul_inv_cancel_left]
      exact hhB
    have key : ∃ j < 16, (gElt j)⁻¹ * elemW g0Word * ((elemW g0Word)⁻¹ * hh) ∈ yK 0 := by
      generalize (elemW g0Word)⁻¹ * hh = c at hcC hcu hB
      obtain ⟨i, hi, j, hj, hcij⟩ := (CzT.mem_iff hP).1 hcC
      have hev : ∀ x (hx : x < 1408), pt (T0 i) (pt (T1 j) x) = (c ⟨x, hx⟩).val := by
        intro x hx
        rw [hcij]
        exact ev_eq hi hj hx
      rcases cellK_spec (cell_at hi hj)
          (bIf_or (hcu.imp (conjB_of hev rU rU1) (conjB_of hev rU rU2))) with
        h704 | ⟨jj, hjj, k, hk, hb⟩
      · exfalso
        have e1 := pt_comp rG0 hev (x := 0) (by norm_num)
        have h0 : ((elemW g0Word * c) ⟨0, by norm_num⟩).val < 704 :=
          (hB ⟨0, by norm_num⟩).2 (by norm_num)
        omega
      · refine ⟨jj, hjj, ?_⟩
        obtain ⟨e0, e1⟩ := isBase_of hb
        have hxk : xY k ∈ yK 0 := (RY.mem (xY k)).2 ⟨k, hk, rfl⟩
        have hdc : (gElt jj)⁻¹ * elemW g0Word * c = xY k :=
          eq_of_base hP (mul_mem (hdC jj hjj) hcC) (hY0le hxk)
            (Fin.ext ((pt_comp (rD jj hjj) hev (by norm_num)).symm.trans
              (e0.trans (Y442202.rc_pt (RY.rc k hk) (by norm_num)))))
            (Fin.ext ((pt_comp (rD jj hjj) hev (by norm_num)).symm.trans
              (e1.trans (Y442202.rc_pt (RY.rc k hk) (by norm_num)))))
        rw [hdc]
        exact hxk
    obtain ⟨j, hj, hm⟩ := key
    refine ⟨j, hj, ?_⟩
    rwa [mul_assoc, mul_inv_cancel_left] at hm
  have killed : ∀ j < 16, j ≠ jStar →
      elemA ∈ closure ({yOne 0, yTwo 0, gElt j} : Set (Equiv.Perm (Fin 1408))) := by
    intro j hj hne
    have hX := rc_lwK (X₁ := Y1) (X₂ := Y2) (X₃ := WK (gWords.getD j [])) (subs := gSubs j)
      (l := (killData.getD j ([], 0)).1)
      (sub3_of (subs := gSubs j) rfl rfl rfl rc_y1 rc_y2 (rc_g hj) (kill_letters j hj))
    have hpow := repC_pow hX (Nat.div (killData.getD j ([], 0)).2 2)
    rw [kill_at hj hne] at hpow
    rw [← eq_of_repC hpow ha]
    refine pow_mem (elemW_expandL_mem (gSubs_mem ?_ ?_ ?_) _) _
    · exact subset_closure (by simp [yOne])
    · exact subset_closure (by simp [yTwo])
    · exact subset_closure (by simp [gElt])
  have fix : ∃ p : Fin 1408, yOne 0 p = p ∧ yTwo 0 p = p ∧ gElt jStar p = p := by
    obtain ⟨hp, h1, h2, h3⟩ := fixK_parts fix_ok
    exact ⟨⟨fixPt, hp⟩, Fin.ext ((repC_pt rc_y1 hp).symm.trans h1),
      Fin.ext ((repC_pt rc_y2 hp).symm.trans h2),
      Fin.ext ((repC_pt (rc_g (j := jStar) (by decide)) hp).symm.trans h3)⟩
  obtain ⟨c7, c9, c125, k7, k9, k125⟩ := syl_cnt
  obtain ⟨Q7, hQ7, h7⟩ := syl_of (i := 0) (by norm_num) (by norm_num) k7 syl7_gens syl7_rec
  obtain ⟨Q9, hQ9, h9⟩ := syl_of (i := 1) (by norm_num) (by norm_num) k9 syl9_gens syl9_rec
  obtain ⟨Q125, hQ125, h125⟩ :=
    syl_of (i := 2) (by norm_num) (by norm_num) k125 syl125_gens syl125_rec
  exact
    { cover := cover
      jStar_lt := by decide
      killed := killed
      fix := fix
      sylow7 := ⟨Q7, hQ7, h7.trans c7⟩
      sylow9 := ⟨Q9, hQ9, h9.trans c9⟩
      sylow125 := ⟨Q125, hQ125, h125.trans c125⟩ }

end CFSG.KD.HN1408.D442204

end
