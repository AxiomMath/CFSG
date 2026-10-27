
module

public import CFSG.Certificates.Kernel.KDense.Glue
public import CFSG.Certificates.Kernel.KDense.SepSound
public import CFSG.Certificates.Kernel.KDense.Tactic
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDense.Data.Sep
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import CFSG.YGroups.Y443.Native.ModFive
public import CFSG.Certificates.Kernel.KDense.Data.SepQ1
public import CFSG.Certificates.Kernel.KDense.Data.SepQ10
public import CFSG.Certificates.Kernel.KDense.Data.SepQ11
public import CFSG.Certificates.Kernel.KDense.Data.SepQ12
public import CFSG.Certificates.Kernel.KDense.Data.SepQ13
public import CFSG.Certificates.Kernel.KDense.Data.SepQ14
public import CFSG.Certificates.Kernel.KDense.Data.SepQ2
public import CFSG.Certificates.Kernel.KDense.Data.SepQ3
public import CFSG.Certificates.Kernel.KDense.Data.SepQ4
public import CFSG.Certificates.Kernel.KDense.Data.SepQ5
public import CFSG.Certificates.Kernel.KDense.Data.SepQ6
public import CFSG.Certificates.Kernel.KDense.Data.SepQ7
public import CFSG.Certificates.Kernel.KDense.Data.SepQ8
public import CFSG.Certificates.Kernel.KDense.Data.SepQ9
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

namespace CertificateChecks.KernelKDense

open CFSG.KC CFSG.KC.KDense CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Griess.ModFive CFSG.YGroups.Y443Native

set_option maxRecDepth 100000

theorem andB_true {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  subst ha; exact hb

@[expose] noncomputable def wit (x : ℕ) : Native.DVec :=
  if x = 0 then aV () else if x = 1 then bV () else wV ()

theorem wV_eq : wV () = ofRange 98580 98581 := by
  unfold wV ofRange
  congr 2
  funext k
  congr 1
  apply propext
  omega

theorem rep_wit {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) : ∀ x < 3, Rep (wit x) (S x) := by
  intro x hx
  rw [hS x hx]
  interval_cases x
  · exact aInit_sound _ _ CFSG.KD.KDF.init_a
  · exact rangeInit_sound _ _ _ CFSG.KD.KDF.init_b
  · rw [show wit 2 = wV () from rfl, wV_eq]
    exact rangeInit_sound _ _ _ CFSG.KD.KDF.init_w

theorem hsep : ∀ c d : ShortIdx, (∀ k ∈ Finset.Icc 1 14,
    qf c ((interpA (aV ()) : Matrix (Fin 24) (Fin 24) ℚ) ^ k) -
      qf d ((interpA (aV ()) : Matrix (Fin 24) (Fin 24) ℚ) ^ k) ∈ D5) → c = d := by
  have h5 : ∀ k ∈ Finset.Icc 1 14, qOK CFSG.KD.KDS.U CFSG.KD.KDS.MK k (CFSG.KD.KDS.QSf k) = true := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨h1, h2⟩ := hk
    interval_cases k
    exacts [CFSG.KD.KDS.q1, CFSG.KD.KDS.q2, CFSG.KD.KDS.q3, CFSG.KD.KDS.q4, CFSG.KD.KDS.q5,
      CFSG.KD.KDS.q6, CFSG.KD.KDS.q7, CFSG.KD.KDS.q8, CFSG.KD.KDS.q9, CFSG.KD.KDS.q10, CFSG.KD.KDS.q11,
      CFSG.KD.KDS.q12, CFSG.KD.KDS.q13, CFSG.KD.KDS.q14]
  exact sep_sound (aTab ()) _ _ _ _ _ _ CFSG.KD.KDF.oct_ok CFSG.KD.KDS.ut_ok CFSG.KD.KDS.u_ok
    CFSG.KD.KDS.mk_ok h5 CFSG.KD.KDS.sort_ok

namespace Y443

open CFSG.YGroups.Y443

theorem eq_of_three {w₁ w₂ : List Native.Gen}
    (h : ∀ x < 3, (∀ g ∈ w₁, g.validB = true) ∧ (∀ g ∈ w₂, g.validB = true) ∧
      Cong5D (Native.evalWord w₁ (wit x)) (Native.evalWord w₂ (wit x))) :
    wordLin w₁ = wordLin w₂ :=
  wordLin_eq_of_cong5D (h 0 (by norm_num)).1 (h 0 (by norm_num)).2.1 hsep (h 0 (by norm_num)).2.2
    (h 1 (by norm_num)).2.2 (h 2 (by norm_num)).2.2

end Y443

theorem words_eq (l : List (List Native.Gen × List Native.Gen)) (s : ℕ) :
    CFSG.KC.KDense.Y443.words l s = Bool.rec (motive := fun _ => List Native.Gen)
      (l.getD (Nat.shiftRight s 1) ([], [])).1 (l.getD (Nat.shiftRight s 1) ([], [])).2
      (Nat.beq (Nat.land s 1) 1) := by
  unfold CFSG.KC.KDense.Y443.words
  generalize Nat.shiftRight s 1 = k
  induction l generalizing k with
  | nil => cases Nat.beq (Nat.land s 1) 1 <;> rfl
  | cons p l ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

theorem words_even (l : List (List Native.Gen × List Native.Gen)) (t : ℕ) :
    CFSG.KC.KDense.Y443.words l (2 * t) = (l.getD t ([], [])).1 := by
  rw [words_eq]
  have h1 : Nat.shiftRight (2 * t) 1 = t := by
    change (2 * t) >>> 1 = t
    rw [Nat.shiftRight_one]; omega
  have h2 : Nat.land (2 * t) 1 = 0 := by
    change (2 * t) &&& 1 = 0
    rw [Nat.and_one_is_mod]; omega
  rw [h1, h2]
  rfl

theorem words_odd (l : List (List Native.Gen × List Native.Gen)) (t : ℕ) :
    CFSG.KC.KDense.Y443.words l (2 * t + 1) = (l.getD t ([], [])).2 := by
  rw [words_eq]
  have h1 : Nat.shiftRight (2 * t + 1) 1 = t := by
    change (2 * t + 1) >>> 1 = t
    rw [Nat.shiftRight_one]; omega
  have h2 : Nat.land (2 * t + 1) 1 = 1 := by
    change (2 * t + 1) &&& 1 = 1
    rw [Nat.and_one_is_mod]; omega
  rw [h1, h2]
  rfl

theorem words_letterOK {l : List (List Native.Gen × List Native.Gen)} (h : pairsLetterOK l = true) :
    ∀ σ, ∀ g ∈ CFSG.KC.KDense.Y443.words l σ, letterOK g = true := by
  intro σ g hg
  rw [words_eq] at hg
  revert hg
  cases Nat.beq (Nat.land σ 1) 1
  · exact (pairsLetterOK_getD h _).1 g
  · exact (pairsLetterOK_getD h _).2 g

end CertificateChecks.KernelKDense

end
