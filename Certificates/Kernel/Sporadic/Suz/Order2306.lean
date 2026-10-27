module

public import Certificates.Kernel.Sporadic.Suz.Chain2306
public import Certificates.Kernel.Sporadic.Suz.RelA2306
public import Certificates.Kernel.Sporadic.Suz.RelB2306
public import Certificates.Kernel.Sporadic.Suz.RelC2306
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs
public import Certificates.Certificate9130
import all CFSG.Sporadic.SuzOddCore.Arrays
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Presentation.Common

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz2306

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres
open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Bridge TauCeti CFSG.KC.Misc.PairCount

theorem relsOK : ∀ v ∈ CFSG.KBRoute.Suz.rels,
    Nat.beq (wordPK 1782 11 Gs GIs v) (pidn 1782 11) = true := by
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
  have hk34 : k < 34 := by simpa [CFSG.KBRoute.Suz.rels] using hk
  rw [← List.getD_eq_getElem _ [] hk]
  interval_cases k
  exacts [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
    r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33]

theorem Gs_ge {i : Nat} (hi : 6 ≤ i) : Gs i = Gs 6 ∧ GIs i = GIs 6 := by
  have h : ∀ j < 6, Nat.beq i j = false := fun j hj => by
    cases hb : Nat.beq i j
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
  unfold Gs GIs
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega)]
  exact ⟨rfl, rfl⟩

theorem imgs_all (i : Nat) : permOK 1782 11 (mask 11) (1782 * 11) (Gs i) (GIs i) = true ∧
    canonK 1782 11 (mask 11) (1782 * 11) (Gs i) = true ∧
    canonK 1782 11 (mask 11) (1782 * 11) (GIs i) = true := by
  rcases Nat.lt_or_ge i 7 with h | h
  · simpa only [bAnd_iff] using allN_spec imgsOK i h
  · obtain ⟨e1, e2⟩ := Gs_ge (i := i) (by omega)
    rw [e1, e2]
    simpa only [bAnd_iff] using allN_spec imgsOK 6 (by norm_num)

@[expose] noncomputable def x (i : Nat) : Equiv.Perm (Fin 1782) := permOfArr 1782 (unpack 1782 11 (Gs i))

theorem rep_x (i : Nat) : Rep 1782 (unpack 1782 11 (Gs i)) (x i) ∧
    Rep 1782 (unpack 1782 11 (GIs i)) (x i)⁻¹ :=
  rep_permOfArr (invEqK_sound (imgs_all i).1).2

theorem idOK : bAnd(canonK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11), idK 1782 11 (mask 11)) =
    true := by
  quickRfl

theorem hid : canonK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) = true ∧
    idK 1782 11 (mask 11) = true :=
  (bAnd_iff (canonK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11)) (idK 1782 11 (mask 11))).1 idOK

theorem relators : ∀ v ∈ Sporadic.suzPresentation.relatorLetters, wordProd x v = 1 := by
  rw [CFSG.KBRoute.Suz.rels_eq]
  exact relators_of_wordPK (fun i => (rep_x i).1) (fun i => (rep_x i).2)
    (fun i => ⟨(imgs_all i).2.1, (imgs_all i).2.2⟩) hid.1 (idK_sound hid.2).symm relsOK

theorem strong01 (j : Nat) (hj : j < 2) : SuzC.S j = SuzSmallT.F j := by
  have h := Nat.eq_of_beq_eq_true (allN_spec strongOK j (by omega))
  rw [h]
  interval_cases j
  · exact Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (SuzSmallT.F 2) (SuzSmallT.F 0) = true)
  · exact Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (SuzSmallT.F 3) (SuzSmallT.F 1) = true)

theorem gen_mem (j : Nat) (hj : j < 2) : permOfArr 1782 smallStrongArrs[j]! ∈
    Subgroup.closure (Set.range fun i : Fin 7 => x i.val) := by
  have hw : ∀ w ∈ [surj0, surj1], ∀ l ∈ w, l.1 < 7 := by decide
  have rp := rep_permOfArr (invEqK_sound (allN_spec perm j (by omega))).2
  rw [strong_eq j (by omega)]
  rw [strong01 j hj] at rp ⊢
  have rw' := fun (w : List (Nat × Bool)) => (rep_wordPK (fun i => (rep_x i).1) (fun i => (rep_x i).2)
    (fun i => ⟨(imgs_all i).2.1, (imgs_all i).2.2⟩) hid.1 (idK_sound hid.2).symm w).1
  interval_cases j
  · have r := rw' surj0
    rw [Nat.eq_of_beq_eq_true surjOK0] at r
    rw [rp.1.unique r]
    exact wordProd_mem_closure surj0 (hw surj0 (by simp))
  · have r := rw' surj1
    rw [Nat.eq_of_beq_eq_true surjOK1] at r
    rw [rp.1.unique r]
    exact wordProd_mem_closure surj1 (hw surj1 (by simp))

theorem orbits : rawOrbitSizes 1782 smallStrongArrs smallBaseNat.toArray =
    [1782, 416, 100, 63, 32, 3] := by
  rw [rawOrbitSizesK_sound binds perm SuzC.hl]
  decide

theorem card_le :
    Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 1782 smallStrongArrs[j.val]!)) ≤
      (rawOrbitSizes 1782 smallStrongArrs smallBaseNat.toArray).prod := by
  have e : SporadicName.Suz.presentation = Sporadic.suzPresentation := rfl
  have hfin : Finite SporadicName.Suz.presentation.Group := Certificates.certificate9130.1.1
  have hcard : Nat.card SporadicName.Suz.presentation.Group ≤ 448345497600 :=
    Certificates.certificate9130.1.2
  rw [e] at hfin hcard
  have hle : Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 1782 smallStrongArrs[j.val]!) ≤
      Subgroup.closure (Set.range fun i : Fin 7 => x i.val) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact gen_mem j.val j.2
  rw [orbits]
  exact (Subgroup.card_le_of_le hle).trans ((card_closure_le_k' Sporadic.suzPresentation
    CFSG.KBRoute.Suz.gens_eq relators).trans (hcard.trans (by norm_num)))

theorem gens_eq : smallGenArrs = smallStrongArrs.extract 0 2 := by
  apply Array.ext (by simp [smallGenArrs, smallStrongArrs])
  intro k h1 h2
  have hk : k < 2 := by simpa [smallGenArrs] using h1
  rw [← getElem!_pos smallGenArrs k h1, Array.getElem_extract,
    ← getElem!_pos smallStrongArrs (0 + k) (by simp [smallStrongArrs]; omega), Nat.zero_add,
    strong_eq k (by omega), strong01 k hk]
  interval_cases k
  · exact smallArr_eq (by norm_num)
  · exact smallArr_eq (by norm_num)

theorem words_eq : smallDerivs = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 12 derivs := by
  decide

@[expose] noncomputable def sift (G : Nat) : Bool :=
  siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G

@[expose] noncomputable def VB0 : Nat := pcomp 1782 11 (mask 11) V (pcomp 1782 11 (mask 11) B0 V)
@[expose] noncomputable def VB1 : Nat := pcomp 1782 11 (mask 11) V (pcomp 1782 11 (mask 11) B1 V)

theorem vOK : bAnd(canonK 1782 11 (mask 11) (1782 * 11) V, bAnd(canonK 1782 11 (mask 11) (1782 * 11) B0,
    bAnd(canonK 1782 11 (mask 11) (1782 * 11) B1,
    bAnd(Nat.beq (pcomp 1782 11 (mask 11) V V) (pidn 1782 11),
    bAnd(bIf(Nat.beq (pg 11 (mask 11) V 0) 0, false, true),
    bAnd(bIf(sift V, false, true),
    bAnd(sift VB0, sift VB1))))))) = true := by
  quickRfl

theorem fixOK : ∀ y < 1782, y = 0 ∨ ∃ j < 12, pg 11 (mask 11) (SuzC.S j) 0 = 0 ∧
    pg 11 (mask 11) (SuzC.S j) y ≠ y := by
  decide +kernel

theorem facts :
    rawChainOK 1782 smallGenArrs smallStrongArrs smallBaseNat.toArray smallDerivs 4 = true ∧
    rawOrbitSizes 1782 smallStrongArrs smallBaseNat.toArray = [1782, 416, 100, 63, 32, 3] ∧
    eqA 1782 (compA 1782 vArr vArr) (idA 1782) = true ∧ vArr[0]! ≠ 0 ∧
    siftA 1782 smallLevels smallBaseNat.toArray 0 vArr = false ∧
    siftA 1782 smallLevels smallBaseNat.toArray 0 (compA 1782 vArr (compA 1782 b0Arr vArr)) =
      true ∧
    siftA 1782 smallLevels smallBaseNat.toArray 0 (compA 1782 vArr (compA 1782 b1Arr vArr)) =
      true ∧
    (∀ x < 1782, x ≠ 0 → ∃ j ∈ levelIdx smallStrongArrs smallBaseNat.toArray 1,
      (smallStrongArrs[j]!)[x]! ≠ x) := by
  obtain ⟨cV, cB0, cB1, hvv, hv0, hsv, hs0, hs1⟩ := (by simpa only [bAnd_iff] using vOK :
    canonK 1782 11 (mask 11) (1782 * 11) V = true ∧ canonK 1782 11 (mask 11) (1782 * 11) B0 = true ∧
    canonK 1782 11 (mask 11) (1782 * 11) B1 = true ∧
    Nat.beq (pcomp 1782 11 (mask 11) V V) (pidn 1782 11) = true ∧
    bIf(Nat.beq (pg 11 (mask 11) V 0) 0, false, true) = true ∧
    bIf(sift V, false, true) = true ∧ sift VB0 = true ∧ sift VB1 = true)
  have hi : ∀ G, canonK 1782 11 (mask 11) (1782 * 11) G = true → Nat.shiftRight G (1782 * 11) = 0 :=
    fun G h => by
      have h' : bAnd(Nat.beq (Nat.shiftRight G (1782 * 11)) (nat_lit 0),
          allN 1782 (fun i => Nat.blt (pg 11 (mask 11) G i) 1782)) = true := h
      exact Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (Nat.shiftRight G (1782 * 11)) (nat_lit 0))
        (allN 1782 (fun i => Nat.blt (pg 11 (mask 11) G i) 1782))).1 h').1
  have c0 : canonK 1782 11 (mask 11) (1782 * 11) VB0 = true := by
    unfold VB0
    exact canonK_pcomp cV (canonK_pcomp cB0 cV)
  have c1 : canonK 1782 11 (mask 11) (1782 * 11) VB1 = true := by
    unfold VB1
    exact canonK_pcomp cV (canonK_pcomp cB1 cV)
  have e0 : compA 1782 vArr (compA 1782 b0Arr vArr) = unpack 1782 11 VB0 := by
    rw [vArr_eq, b0Arr_eq, compA_unpack cB0 cV, compA_unpack cV (canonK_pcomp cB0 cV)]
    rfl
  have e1 : compA 1782 vArr (compA 1782 b1Arr vArr) = unpack 1782 11 VB1 := by
    rw [vArr_eq, b1Arr_eq, compA_unpack cB1 cV, compA_unpack cV (canonK_pcomp cB1 cV)]
    rfl
  refine ⟨?_, orbits, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gens_eq, words_eq]
    exact rawChainK_of_card 4 binds SuzC.head SuzC.hl card_le
  · rw [vArr_eq, compA_unpack cV cV, (idK_sound hid.2).symm,
      eqA_unpack (canonK_pcomp cV cV) hid.1]
    exact hvv
  · rw [vArr_eq, unpack_get (by norm_num)]
    intro h
    rw [h] at hv0
    exact absurd hv0 (by decide)
  · rw [smallLevels, siftK_eq binds perm SuzC.hl vArr_eq (hi V cV) (range_of_canonK cV)]
    change sift V = false
    cases h : sift V
    · rfl
    · rw [h] at hsv
      exact absurd hsv (by decide)
  · rw [smallLevels, e0]
    exact siftK_soundR binds perm SuzC.hl rfl (hi _ c0) (range_of_canonK c0) hs0
  · rw [smallLevels, e1]
    exact siftK_soundR binds perm SuzC.hl rfl (hi _ c1) (range_of_canonK c1) hs1
  · intro y hy hy0
    rcases fixOK y hy with h | ⟨j, hj, h0, hm⟩
    · exact absurd h hy0
    · refine ⟨j, ?_, ?_⟩
      · rw [levelIdx, List.mem_filter, List.mem_range]
        refine ⟨by simpa [smallStrongArrs] using hj, ?_⟩
        rw [strong_eq j hj]
        simp [fixesFirst, allLt, smallBaseNat, unpack_get, h0]
      · rw [strong_eq j hj, unpack_get hy]
        exact hm

end CertificateChecks.KernelSpor.Suz2306

end
