module

public import Certificates.Kernel.Sporadic.Suz.EndChecks
public import Certificates.Kernel.Sporadic.Suz.EndChain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndK
public import CFSG.Certificates.Kernel.SporSch.ChainKClasses
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Sporadic.SuzOddCore.InvCentralizers
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzEnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.ComponentClassification.RankTwoSporadic.Suz CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.RankTwoSporadic.Endgame CFSG.Sporadic.Schreier
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open scoped commutatorElement

theorem prep_of {P PI : Nat} (h : permOK 1782 11 (mask 11) (1782 * 11) P PI = true) :
    PRep 1782 11 P (permOfArr 1782 (unpack 1782 11 P)) ∧
      PRep 1782 11 PI (permOfArr 1782 (unpack 1782 11 P))⁻¹ := by
  have hr := rep_permOfArr (isInvA_unpack h)
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

theorem ap {P : Nat} {x : Equiv.Perm (Fin 1782)} (h : PRep 1782 11 P x) (p : Fin 1782) :
    ((x p : Fin 1782) : ℕ) = fv P p := (h p).symm

theorem ext1782 {x y : Equiv.Perm (Fin 1782)}
    (h : ∀ p : Fin 1782, ((x p : Fin 1782) : ℕ) = y p) : x = y :=
  Equiv.ext fun p => Fin.ext (h p)

theorem beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ne_spec {a b : Nat} (h : ne a b = true) : a ≠ b := by
  intro e
  subst e
  unfold ne at h
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem imageList_of_rep {n : Nat} {t : Array Nat} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (h : Rep n t g) : CFSG.Monster.B.Mathieu.imageList g = t.toList := by
  apply List.ext_getElem
  · simp [CFSG.Monster.B.Mathieu.imageList, ht]
  · intro i h1 h2
    have hi : i < n := by simpa [CFSG.Monster.B.Mathieu.imageList] using h1
    simp only [CFSG.Monster.B.Mathieu.imageList, List.getElem_ofFn, Array.getElem_toList]
    rw [← h.apply hi, getElem!_pos t i (by omega)]

theorem isInv_of {P PI : Nat} (h : permOK 1782 11 (mask 11) (1782 * 11) P PI = true) :
    isInvA 1782 (unpack 1782 11 P) (invCand 1782 (unpack 1782 11 P)) = true := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Prim.invEqK_sound (r := PI) h
  rw [h1]
  exact h2

theorem inMA_of {P PI : Nat} (hp : permOK 1782 11 (mask 11) (1782 * 11) P PI = true)
    (hs : Suz2306.sift P = true) : suzInMA (unpack 1782 11 P) := by
  refine ⟨isInv_of hp, ?_⟩
  unfold suzInM
  rw [smallLevels]
  exact siftK_soundR Suz2306.binds Suz2306.perm SuzC.hl rfl (permOK_facts hp).1
    (range_of_permOK hp) hs

theorem fix_eq {P : Nat} {x : Equiv.Perm (Fin 1782)} (hx : PRep 1782 11 P x) :
    fix1782 x = fc P := by
  rw [fix1782, ← fixedCount_eq (rep_unpack hx), fixedCount_unpack]
  rfl

section Generic

variable {P Q PI QI : Nat} {x y : Equiv.Perm (Fin 1782)}

theorem sq_of (hx : PRep 1782 11 P x) (h : ∀ p : Fin 1782, Nat.beq (fv P (fv P p)) p = true) :
    x * x = 1 :=
  ext1782 fun p => by
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, ap hx]
    exact beq_eq (h p)

theorem comm_of (hx : PRep 1782 11 P x) (hy : PRep 1782 11 Q y)
    (h : ∀ p : Fin 1782, Nat.beq (fv P (fv Q p)) (fv Q (fv P p)) = true) : x * y = y * x :=
  ext1782 fun p => by
    simp only [Equiv.Perm.mul_apply, ap hx, ap hy]
    exact beq_eq (h p)

theorem ncomm_of (hx : PRep 1782 11 P x) (hy : PRep 1782 11 Q y)
    (h : ∃ p < 1782, ne (fv P (fv Q p)) (fv Q (fv P p)) = true) : x * y ≠ y * x := fun e => by
  obtain ⟨p, hp, hn⟩ := h
  have := congrArg (fun g : Equiv.Perm (Fin 1782) => ((g ⟨p, hp⟩ : Fin 1782) : ℕ)) e
  simp only [Equiv.Perm.mul_apply, ap hx, ap hy] at this
  exact ne_spec hn this

theorem conj_of {C CI T : Nat} {c t e : Equiv.Perm (Fin 1782)} (hc : PRep 1782 11 C c)
    (hci : PRep 1782 11 CI c⁻¹) (he : PRep 1782 11 P e) (ht : PRep 1782 11 T t)
    (h : ∀ p : Fin 1782, Nat.beq (fv C (fv P (fv CI p))) (fv T p) = true) : c * e * c⁻¹ = t :=
  ext1782 fun p => by
    simp only [Equiv.Perm.mul_apply, ap hc, ap hci, ap he, ap ht]
    exact beq_eq (h p)

variable {b e e' : Equiv.Perm (Fin 1782)}

theorem conjComm_of (hb : PRep 1782 11 B b) (hbi : PRep 1782 11 BI b⁻¹) (he : PRep 1782 11 P e)
    (he' : PRep 1782 11 Q e') (h : ∀ p : Fin 1782, cB P Q p = true) :
    e * (b⁻¹ * e' * b) = b⁻¹ * e' * b * e :=
  ext1782 fun p => by
    simp only [Equiv.Perm.mul_apply, ap hb, ap hbi, ap he, ap he']
    exact beq_eq (h p)

theorem cC_eq (hb : PRep 1782 11 B b) (hbi : PRep 1782 11 BI b⁻¹) (he : PRep 1782 11 E0 e)
    (p : Fin 1782) : (((b⁻¹ * e * b) p : Fin 1782) : ℕ) = cC p := by
  simp only [Equiv.Perm.mul_apply, ap hb, ap hbi, ap he]
  rfl

theorem conjNe_of (hb : PRep 1782 11 B b) (hbi : PRep 1782 11 BI b⁻¹) (he : PRep 1782 11 E0 e)
    {f : Equiv.Perm (Fin 1782)} {F : Nat → Nat} (hf : ∀ p : Fin 1782, ((f p : Fin 1782) : ℕ) = F p)
    (h : ∃ p < 1782, ne (cC p) (F p) = true) : b⁻¹ * e * b ≠ f := fun hc => by
  obtain ⟨p, hp, hn⟩ := h
  have := congrArg (fun g : Equiv.Perm (Fin 1782) => ((g ⟨p, hp⟩ : Fin 1782) : ℕ)) hc
  rw [cC_eq hb hbi he, hf] at this
  exact ne_spec hn this

theorem comm_eq {C : Nat} {c : Equiv.Perm (Fin 1782)} (hx : PRep 1782 11 P x)
    (hxi : PRep 1782 11 PI x⁻¹) (hy : PRep 1782 11 Q y) (hyi : PRep 1782 11 QI y⁻¹)
    (hc : PRep 1782 11 C c) (h : ∀ p : Fin 1782, Nat.beq (fv C p) (cm P Q PI QI p) = true) :
    c = ⁅x, y⁆ :=
  ext1782 fun p => by
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply, ap hx, ap hy, ap hxi, ap hyi, ap hc]
    exact beq_eq (h p)

theorem top_eq (hx : PRep 1782 11 P x) (hxi : PRep 1782 11 PI x⁻¹) (hy : PRep 1782 11 Q y)
    (hyi : PRep 1782 11 QI y⁻¹) (hb : PRep 1782 11 B b) (hbi : PRep 1782 11 BI b⁻¹)
    (he : PRep 1782 11 E0 e)
    (h : ∀ p : Fin 1782, Nat.beq (cm P Q PI QI p) (fv E0 (cC p)) = true) :
    ⁅x, y⁆ = e * (b⁻¹ * e * b) :=
  ext1782 fun p => by
    rw [commutatorElement_def, Equiv.Perm.mul_apply e, ap he, cC_eq hb hbi he]
    simp only [Equiv.Perm.mul_apply, ap hx, ap hy, ap hxi, ap hyi]
    exact beq_eq (h p)

@[expose] def wperm (g₀ g₁ : Equiv.Perm (Fin 1782)) : List Nat → Equiv.Perm (Fin 1782)
  | [] => 1
  | i :: w => wperm g₀ g₁ w * (if i = 0 then g₀ else g₁)

theorem wperm_apply {g₀ g₁ : Equiv.Perm (Fin 1782)} (h0 : PRep 1782 11 (SuzEL.S 0) g₀)
    (h1 : PRep 1782 11 (SuzEL.S 1) g₁) :
    ∀ (w : List Nat) (p : Fin 1782), ((wperm g₀ g₁ w p : Fin 1782) : ℕ) = wpt w p
  | [], p => rfl
  | i :: w, p => by
    rw [wperm, Equiv.Perm.mul_apply, wperm_apply h0 h1 w]
    change wpt w _ = wpt w (fv (nIf(Nat.beq i 0, SuzEL.S 0, SuzEL.S 1)) p)
    congr 1
    by_cases hi : i = 0
    · subst hi
      rw [ite_eq_left (e := g₁) rfl, ap h0]
      rfl
    · rw [ite_eq_right (t := g₀) hi, ap h1]
      have : Nat.beq i 0 = false := by
        cases h : Nat.beq i 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hi
      rw [this]

theorem wperm_mem {H : Subgroup (Equiv.Perm (Fin 1782))} {g₀ g₁ : Equiv.Perm (Fin 1782)}
    (h0 : g₀ ∈ H) (h1 : g₁ ∈ H) : ∀ w : List Nat, wperm g₀ g₁ w ∈ H
  | [] => H.one_mem
  | i :: w => by
    rw [wperm]
    refine H.mul_mem (wperm_mem h0 h1 w) ?_
    split
    · exact h0
    · exact h1

theorem fix_of {Z : Nat} {z : Equiv.Perm (Fin 1782)} (hZ : PRep 1782 11 Z z)
    (h : bor (anyN 1782 fun p => ne (fv Z (fv Z p)) p)
      (bor (allN 1782 fun p => Nat.beq (fv Z p) p) (ne (fc Z) 42)) = true)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : fix1782 z ≠ 42 := by
  have h1 : anyN 1782 (fun p => ne (fv Z (fv Z p)) p) = false := by
    cases ha : anyN 1782 (fun p => ne (fv Z (fv Z p)) p)
    · rfl
    · obtain ⟨p, hp, hn⟩ := anyN_spec ha
      have := congrArg (fun f : Equiv.Perm (Fin 1782) => ((f ⟨p, hp⟩ : Fin 1782) : ℕ)) hz2
      simp only [sq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, ap hZ] at this
      exact absurd this (ne_spec hn)
  have h2 : allN 1782 (fun p => Nat.beq (fv Z p) p) = false := by
    cases ha : allN 1782 (fun p => Nat.beq (fv Z p) p)
    · rfl
    · refine absurd (ext1782 fun p => ?_) hz1
      rw [ap hZ, Equiv.Perm.one_apply]
      exact beq_eq (CFSG.KS.allN_spec ha p p.2)
  unfold bor at h
  rw [h1] at h
  change bIf(allN 1782 (fun p => Nat.beq (fv Z p) p), true, ne (fc Z) 42) = true at h
  rw [h2] at h
  rw [fix_eq hZ]
  exact ne_spec h

end Generic

theorem pFacts : permOK 1782 11 (mask 11) (1782 * 11) E0 (EI 0) = true ∧
    permOK 1782 11 (mask 11) (1782 * 11) E1 (EI 1) = true ∧
    permOK 1782 11 (mask 11) (1782 * 11) B BI = true ∧
    permOK 1782 11 (mask 11) (1782 * 11) T0 T0 = true ∧
    (∀ i < 2, permOK 1782 11 (mask 11) (1782 * 11) (SG i) (SGI i) = true) ∧
    (∀ i < 8, permOK 1782 11 (mask 11) (1782 * 11) (X i) (XI i) = true) ∧
    ∀ i < 6, permOK 1782 11 (mask 11) (1782 * 11) (Y i) (YI i) = true := by
  have h := pOK
  unfold pK at h
  simp only [CFSG.KS.bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, CFSG.KS.allN_spec h5, CFSG.KS.allN_spec h6, CFSG.KS.allN_spec h7⟩

theorem mFacts : Suz2306.sift E0 = true ∧ Suz2306.sift E1 = true ∧ Suz2306.sift B = true ∧
    Suz2306.sift (SG 0) = true ∧ Suz2306.sift (SG 1) = true := by
  have h := mOK
  unfold mK at h
  simpa only [CFSG.KS.bAnd_iff] using h

theorem e_eq {i : Nat} (hi : i < 2) : suzE0[i]! = unpack 1782 11 (SuzEndE.F i) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzEndE.all i hi
  rw [← SuzEndE.eq] at h
  interval_cases i
  · rw [Nat.mul_zero] at h
    rw [← h]
    rfl
  · rw [Nat.mul_one] at h
    rw [← h]
    rfl

theorem hE0 : suzEndE 0 = permOfArr 1782 (unpack 1782 11 E0) := by
  rw [suzEndE, e_eq (by norm_num)]
  rfl

theorem hE1 : suzEndE 1 = permOfArr 1782 (unpack 1782 11 E1) := by
  rw [suzEndE, e_eq (by norm_num)]
  rfl

theorem pE0 : PRep 1782 11 E0 (suzEndE 0) := by rw [hE0]; exact (prep_of pFacts.1).1

theorem pE1 : PRep 1782 11 E1 (suzEndE 1) := by rw [hE1]; exact (prep_of pFacts.2.1).1

theorem eAt (p : Fin 1782) : Nat.beq (fv E0 (fv E0 p)) p = true ∧
    Nat.beq (fv E1 (fv E1 p)) p = true ∧ Nat.beq (fv E0 (fv E1 p)) (fv E1 (fv E0 p)) = true := by
  have h := eOK
  unfold eK at h
  have := CFSG.KS.allN_spec h p p.2
  simpa only [CFSG.KS.bAnd_iff] using this

theorem e_fix : fix1782 (suzEndE 0) = 42 ∧ fix1782 (suzEndE 1) = 42 ∧
    fix1782 (suzEndE 0 * suzEndE 1) = 42 := by
  have h := fOK
  unfold fK at h
  simp only [CFSG.KS.bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [fix_eq pE0, beq_eq h1], by rw [fix_eq pE1, beq_eq h2], ?_⟩
  rw [fix_eq (prep_pcomp (by norm_num) pE0 pE1), beq_eq h3]

theorem bcAt (p : Fin 1782) : cB E0 E0 p = true ∧ cB E0 E1 p = true ∧ cB E1 E0 p = true ∧
    cB E1 E1 p = true := by
  have h := bcOK
  unfold bcK at h
  have := CFSG.KS.allN_spec h p p.2
  simpa only [CFSG.KS.bAnd_iff] using this

theorem bn_facts : (∃ p < 1782, ne (cC p) p = true) ∧ (∃ p < 1782, ne (cC p) (fv E0 p) = true) ∧
    (∃ p < 1782, ne (cC p) (fv E1 p) = true) ∧
    ∃ p < 1782, ne (cC p) (fv E0 (fv E1 p)) = true := by
  have h := bnOK
  unfold bnK at h
  simp only [CFSG.KS.bAnd_iff] at h
  exact ⟨anyN_spec h.1, anyN_spec h.2.1, anyN_spec h.2.2.1, anyN_spec h.2.2.2⟩

theorem xcAt {i : Nat} (hi : i < 8) (p : Fin 1782) :
    Nat.beq (fv (X i) (fv E0 p)) (fv E0 (fv (X i) p)) = true ∧
      Nat.beq (fv (X i) (fv E1 p)) (fv E1 (fv (X i) p)) = true := by
  have h := xcOK
  unfold xcK at h
  have := CFSG.KS.allN_spec (CFSG.KS.allN_spec h i hi) p p.2
  simpa only [CFSG.KS.bAnd_iff] using this

theorem trAt (p : Fin 1782) :
    (∀ j < 4, Nat.beq (fv (Y j) p) (cm (X (Nat.mul 2 j)) (X (Nat.add (Nat.mul 2 j) 1))
      (XI (Nat.mul 2 j)) (XI (Nat.add (Nat.mul 2 j) 1)) p) = true) ∧
    Nat.beq (fv (Y 4) p) (cm (Y 0) (Y 1) (YI 0) (YI 1) p) = true ∧
    Nat.beq (fv (Y 5) p) (cm (Y 2) (Y 3) (YI 2) (YI 3) p) = true ∧
    Nat.beq (cm (Y 4) (Y 5) (YI 4) (YI 5) p) (fv E0 (cC p)) = true := by
  have h := trOK
  unfold trK at h
  have := CFSG.KS.allN_spec h p p.2
  simp only [CFSG.KS.bAnd_iff] at this
  exact ⟨CFSG.KS.allN_spec this.1, this.2⟩

@[expose] noncomputable def xP (i : Nat) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (unpack 1782 11 (X i))

@[expose] noncomputable def yP (i : Nat) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (unpack 1782 11 (Y i))

@[expose] noncomputable def bP : Equiv.Perm (Fin 1782) := permOfArr 1782 (unpack 1782 11 B)

theorem pX {i : Nat} (hi : i < 8) : PRep 1782 11 (X i) (xP i) ∧ PRep 1782 11 (XI i) (xP i)⁻¹ :=
  prep_of (pFacts.2.2.2.2.2.1 i hi)

theorem pY {i : Nat} (hi : i < 6) : PRep 1782 11 (Y i) (yP i) ∧ PRep 1782 11 (YI i) (yP i)⁻¹ :=
  prep_of (pFacts.2.2.2.2.2.2 i hi)

theorem pB : PRep 1782 11 B bP ∧ PRep 1782 11 BI bP⁻¹ := prep_of pFacts.2.2.1

theorem y_eq {j : Nat} (hj : j < 4) : yP j = ⁅xP (2 * j), xP (2 * j + 1)⁆ :=
  comm_eq (pX (i := 2 * j) (by omega)).1 (pX (i := 2 * j) (by omega)).2
    (pX (i := 2 * j + 1) (by omega)).1 (pX (i := 2 * j + 1) (by omega)).2 (pY (by omega)).1
    fun p => (trAt p).1 j hj

theorem tree_eq : tree3 (fun i : Fin 8 => xP i) = suzEndE 0 * (bP⁻¹ * suzEndE 0 * bP) := by
  have h4 : yP 4 = ⁅yP 0, yP 1⁆ := comm_eq (pY (by norm_num)).1 (pY (by norm_num)).2
    (pY (by norm_num)).1 (pY (by norm_num)).2 (pY (by norm_num)).1 fun p => (trAt p).2.1
  have h5 : yP 5 = ⁅yP 2, yP 3⁆ := comm_eq (pY (by norm_num)).1 (pY (by norm_num)).2
    (pY (by norm_num)).1 (pY (by norm_num)).2 (pY (by norm_num)).1 fun p => (trAt p).2.2.1
  have ht : ⁅yP 4, yP 5⁆ = suzEndE 0 * (bP⁻¹ * suzEndE 0 * bP) :=
    top_eq (pY (by norm_num)).1 (pY (by norm_num)).2 (pY (by norm_num)).1 (pY (by norm_num)).2
      pB.1 pB.2 pE0 fun p => (trAt p).2.2.2
  have y0 : yP 0 = ⁅xP 0, xP 1⁆ := y_eq (j := 0) (by norm_num)
  have y1 : yP 1 = ⁅xP 2, xP 3⁆ := y_eq (j := 1) (by norm_num)
  have y2 : yP 2 = ⁅xP 4, xP 5⁆ := y_eq (j := 2) (by norm_num)
  have y3 : yP 3 = ⁅xP 6, xP 7⁆ := y_eq (j := 3) (by norm_num)
  rw [tree3]
  change ⁅⁅⁅xP 0, xP 1⁆, ⁅xP 2, xP 3⁆⁆, ⁅⁅xP 4, xP 5⁆, ⁅xP 6, xP 7⁆⁆⁆ = _
  rw [← y0, ← y1, ← y2, ← y3, ← h4, ← h5, ht]

theorem conj_facts : ∃ b : Array ℕ, ∃ x : Fin 8 → Array ℕ, suzInMA b ∧ (∀ i, suzInMA (x i)) ∧
    (∀ i < 2, ∀ j < 2, suzEndE i * ((permOfArr 1782 b)⁻¹ * suzEndE j * permOfArr 1782 b) =
      (permOfArr 1782 b)⁻¹ * suzEndE j * permOfArr 1782 b * suzEndE i) ∧
    (permOfArr 1782 b)⁻¹ * suzEndE 0 * permOfArr 1782 b ∉
      ({1, suzEndE 0, suzEndE 1, suzEndE 0 * suzEndE 1} : Set (Equiv.Perm (Fin 1782))) ∧
    (∀ i, ∀ j < 2, permOfArr 1782 (x i) * suzEndE j = suzEndE j * permOfArr 1782 (x i)) ∧
    tree3 (fun i => permOfArr 1782 (x i)) =
      suzEndE 0 * ((permOfArr 1782 b)⁻¹ * suzEndE 0 * permOfArr 1782 b) := by
  obtain ⟨⟨p1, hp1, n1⟩, ⟨p2, hp2, n2⟩, ⟨p3, hp3, n3⟩, ⟨p4, hp4, n4⟩⟩ := bn_facts
  refine ⟨unpack 1782 11 B, fun i => unpack 1782 11 (X i.val), inMA_of pFacts.2.2.1 mFacts.2.2.1,
    fun i => inMA_of (pFacts.2.2.2.2.2.1 i i.2) (SuzEndMX.all i i.2), fun i hi j hj => ?_, ?_,
    fun i j hj => ?_, tree_eq⟩
  · change suzEndE i * (bP⁻¹ * suzEndE j * bP) = bP⁻¹ * suzEndE j * bP * suzEndE i
    interval_cases i <;> interval_cases j
    · exact conjComm_of pB.1 pB.2 pE0 pE0 fun p => (bcAt p).1
    · exact conjComm_of pB.1 pB.2 pE0 pE1 fun p => (bcAt p).2.1
    · exact conjComm_of pB.1 pB.2 pE1 pE0 fun p => (bcAt p).2.2.1
    · exact conjComm_of pB.1 pB.2 pE1 pE1 fun p => (bcAt p).2.2.2
  · change bP⁻¹ * suzEndE 0 * bP ∉ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨conjNe_of pB.1 pB.2 pE0 (F := fun p => p) (fun p => rfl) ⟨p1, hp1, n1⟩,
      conjNe_of pB.1 pB.2 pE0 (ap pE0) ⟨p2, hp2, n2⟩,
      conjNe_of pB.1 pB.2 pE0 (ap pE1) ⟨p3, hp3, n3⟩,
      conjNe_of pB.1 pB.2 pE0 (F := fun p => fv E0 (fv E1 p))
        (fun p => by rw [Equiv.Perm.mul_apply, ap pE0, ap pE1]) ⟨p4, hp4, n4⟩⟩
  · change xP i * suzEndE j = suzEndE j * xP i
    interval_cases j
    · exact comm_of (pX i.2).1 pE0 fun p => (xcAt i.2 p).1
    · exact comm_of (pX i.2).1 pE1 fun p => (xcAt i.2 p).2

@[expose] noncomputable def gensL : List (Equiv.Perm (Fin 1782)) :=
  (List.range 4).map fun j => permOfArr 1782 (unpack 1782 11 (SuzEL.S j))

@[expose] noncomputable def arrL : Array (Array ℕ) := Array.ofFn (n := 4) fun j =>
  unpack 1782 11 (SuzEL.S j.val)

@[expose] noncomputable def gensS : List (Equiv.Perm (Fin 1782)) :=
  (List.range 4).map fun j => permOfArr 1782 (unpack 1782 11 (SuzES.S j))

@[expose] noncomputable def arrS : Array (Array ℕ) := Array.ofFn (n := 4) fun j =>
  unpack 1782 11 (SuzES.S j.val)

theorem pL {j : Nat} (hj : j < 4) :
    permOK 1782 11 (mask 11) (1782 * 11) (SuzEL.S j) (SuzEL.SI j) = true :=
  CFSG.KS.allN_spec (head_facts SuzEL.head).1 j hj

theorem pS {j : Nat} (hj : j < 4) :
    permOK 1782 11 (mask 11) (1782 * 11) (SuzES.S j) (SuzES.SI j) = true :=
  CFSG.KS.allN_spec (head_facts SuzES.head).1 j hj

theorem nsL : 1782 ≤ SuzEL.NS * 16 := Nat.le_of_ble_eq_true (by quickRfl)

theorem nsS : 1782 ≤ SuzES.NS * 4 := Nat.le_of_ble_eq_true (by quickRfl)

theorem chainL : ChainK 1782 11 gensL noDerivs (#v[0, 1] : Vector (Fin 1782) 2) SuzEL.S SuzEL.SI
    SuzEL.LR SuzEL.TR SuzEL.TRI 4 SuzEL.BP SuzEL.NS 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, SuzEL.head, SuzEL.hl,
    nsL, SuzEL.hs⟩
  have hj4 : j < 4 := by simpa [gensL] using hj
  rw [List.getD_eq_getElem _ _ hj]
  simp only [gensL, List.getElem_map, List.getElem_range]
  exact imageList_of_rep (by simp [unpack]) (rep_permOfArr (isInvA_unpack (pL hj4))).1

theorem chainS : ChainK 1782 11 gensS noDerivs (#v[0] : Vector (Fin 1782) 1) SuzES.S SuzES.SI
    SuzES.LR SuzES.TR SuzES.TRI 4 SuzES.BP SuzES.NS 4 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, SuzES.head, SuzES.hl,
    nsS, SuzES.hs⟩
  have hj4 : j < 4 := by simpa [gensS] using hj
  rw [List.getD_eq_getElem _ _ hj]
  simp only [gensS, List.getElem_map, List.getElem_range]
  exact imageList_of_rep (by simp [unpack]) (rep_permOfArr (isInvA_unpack (pS hj4))).1

theorem hbsL : (#v[0, 1] : Vector (Fin 1782) 2).toList.Nodup := by decide

theorem hbsS : (#v[0] : Vector (Fin 1782) 1).toList.Nodup := by decide

theorem arrL_get {k : Nat} (hk : k < 4) : arrL[k]! = unpack 1782 11 (SuzEL.S k) := by
  rw [arrL, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem arrS_get {k : Nat} (hk : k < 4) : arrS[k]! = unpack 1782 11 (SuzES.S k) := by
  rw [arrS, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem permsA_arrL : permsA 1782 arrL = {g | g ∈ gensL} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, gensL, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk4 : k < 4 := by simpa [arrL] using hk
    exact ⟨k, hk4, by rw [arrL_get hk4]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [arrL] using hk, by rw [arrL_get hk]⟩

theorem permsA_arrS : permsA 1782 arrS = {g | g ∈ gensS} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, gensS, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk4 : k < 4 := by simpa [arrS] using hk
    exact ⟨k, hk4, by rw [arrS_get hk4]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [arrS] using hk, by rw [arrS_get hk]⟩

theorem closure_arrL : Subgroup.closure (permsA 1782 arrL) =
    (certificate (by norm_num) gensL noDerivs (#v[0, 1] : Vector (Fin 1782) 2) hbsL).originalSubgroup := by
  rw [certificate_originalSubgroup, permsA_arrL]

theorem closure_arrS : Subgroup.closure (permsA 1782 arrS) =
    (certificate (by norm_num) gensS noDerivs (#v[0] : Vector (Fin 1782) 1) hbsS).originalSubgroup := by
  rw [certificate_originalSubgroup, permsA_arrS]

theorem ordL : ordK SuzEL.LR 2 = 20160 := by
  have h := cntL
  simp only [CFSG.KS.bAnd_iff] at h
  have e : ordK SuzEL.LR 2 = rcnt (SuzEL.LR 1) * (rcnt (SuzEL.LR 0) * 1) := rfl
  rw [e, beq_eq h.1, beq_eq h.2]

theorem ordS : ordK SuzES.LR 1 = 64 := by
  have e : ordK SuzES.LR 1 = rcnt (SuzES.LR 0) * 1 := rfl
  rw [e, beq_eq cntS]

theorem lgrp_facts (hel : ∀ j < 64, elemOK j = true) : ∃ l : Array (Array ℕ),
    (∀ k < l.size, suzInMA l[k]! ∧
      ∀ j < 2, permOfArr 1782 l[k]! * suzEndE j = suzEndE j * permOfArr 1782 l[k]!) ∧
    Nat.card (Subgroup.closure (permsA 1782 l)) = 20160 ∧
    ∃ s : Array (Array ℕ), (∀ k < s.size, permOfArr 1782 s[k]! ∈ Subgroup.closure (permsA 1782 l)) ∧
      Nat.card (Subgroup.closure (permsA 1782 s)) = 64 ∧
      ∀ z ∈ Subgroup.closure (permsA 1782 s), z ^ 2 = 1 → z ≠ 1 → fix1782 z ≠ 42 := by
  have hl0 := (prep_of (pL (j := 0) (by norm_num))).1
  have hl1 := (prep_of (pL (j := 1) (by norm_num))).1
  have hmem : ∀ k < 4, permOfArr 1782 (unpack 1782 11 (SuzEL.S k)) ∈
      Subgroup.closure (permsA 1782 arrL) := fun k hk =>
    Subgroup.subset_closure ⟨k, by simpa [arrL] using hk, by simp only [arrL_get hk]⟩
  refine ⟨arrL, fun k hk => ?_, ?_, arrS, fun k hk => ?_, ?_, ?_⟩
  · have hk4 : k < 4 := by simpa [arrL] using hk
    rw [arrL_get hk4]
    refine ⟨inMA_of (pL hk4) (SuzEndML.all k hk4), fun j hj => ?_⟩
    have h := lcOK
    unfold lcK at h
    have hs := (prep_of (pL hk4)).1
    interval_cases j
    · exact comm_of hs pE0 fun p => (by
        have := CFSG.KS.allN_spec (CFSG.KS.allN_spec h k hk4) p p.2
        simp only [CFSG.KS.bAnd_iff] at this
        exact this.1)
    · exact comm_of hs pE1 fun p => (by
        have := CFSG.KS.allN_spec (CFSG.KS.allN_spec h k hk4) p p.2
        simp only [CFSG.KS.bAnd_iff] at this
        exact this.2)
  · rw [closure_arrL, card_group chainL (by norm_num) hbsL, ordL]
  · have hk4 : k < 4 := by simpa [arrS] using hk
    rw [arrS_get hk4]
    have hw : permOfArr 1782 (unpack 1782 11 (SuzES.S k)) =
        wperm (permOfArr 1782 (unpack 1782 11 (SuzEL.S 0)))
          (permOfArr 1782 (unpack 1782 11 (SuzEL.S 1))) (nthW suzEndSWords k) := by
      have hs := (prep_of (pS hk4)).1
      refine ext1782 fun p => ?_
      rw [ap hs, wperm_apply hl0 hl1]
      exact beq_eq (CFSG.KS.allN_spec (SuzEndSW.all k hk4) p p.2)
    rw [hw]
    exact wperm_mem (hmem 0 (by norm_num)) (hmem 1 (by norm_num)) _
  · rw [closure_arrS, card_group chainS (by norm_num) hbsS, ordS]
  · intro z hz hz2 hz1
    rw [closure_arrS] at hz
    obtain ⟨j, hj, rfl⟩ := (mem_group_iff chainS (by norm_num) hbsS z).1 hz
    rw [ordS] at hj
    have h := hel j hj
    unfold elemOK at h
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h
    exact fix_of (prep_elemK chainS j) h hz2 hz1

theorem sg_facts : (∃ σ : Array ℕ, suzInMA σ ∧
      permOfArr 1782 σ * suzEndE 0 = suzEndE 0 * permOfArr 1782 σ ∧
      permOfArr 1782 σ * suzEndE 1 ≠ suzEndE 1 * permOfArr 1782 σ) ∧
    ∃ c : Array ℕ, suzInMA c ∧
      permOfArr 1782 c * suzEndE 0 * (permOfArr 1782 c)⁻¹ = permOfArr 1782 (tArr 0) := by
  have h := sgOK
  unfold sgK at h
  simp only [CFSG.KS.bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hs := prep_of (pFacts.2.2.2.2.1 0 (by norm_num))
  have hc := prep_of (pFacts.2.2.2.2.1 1 (by norm_num))
  have ht : PRep 1782 11 T0 (permOfArr 1782 (tArr 0)) := by
    rw [(rep_facts (i := 0) (by norm_num)).1]
    exact (prep_of pFacts.2.2.2.1).1
  refine ⟨⟨unpack 1782 11 (SG 0), inMA_of (pFacts.2.2.2.2.1 0 (by norm_num)) mFacts.2.2.2.1,
    comm_of hs.1 pE0 fun p => CFSG.KS.allN_spec h1 p p.2, ncomm_of hs.1 pE1 (anyN_spec h2)⟩,
    unpack 1782 11 (SG 1), inMA_of (pFacts.2.2.2.2.1 1 (by norm_num)) mFacts.2.2.2.2,
    conj_of hc.1 hc.2 pE0 ht fun p => CFSG.KS.allN_spec h3 p p.2⟩

theorem suzEndFactsK_of (hel : ∀ j < 64, elemOK j = true) : SuzEndFactsK := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, comm_of pE0 pE1 fun p => (eAt p).2.2, e_fix,
    conj_facts, lgrp_facts hel, sg_facts.1, sg_facts.2⟩
  · interval_cases i
    · rw [e_eq (by norm_num)]
      exact inMA_of pFacts.1 mFacts.1
    · rw [e_eq (by norm_num)]
      exact inMA_of pFacts.2.1 mFacts.2.1
  · interval_cases i
    · exact sq_of pE0 fun p => (eAt p).1
    · exact sq_of pE1 fun p => (eAt p).2.1

end CertificateChecks.KernelSpor.SuzEnd

end
