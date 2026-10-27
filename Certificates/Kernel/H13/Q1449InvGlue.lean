module

public import CFSG.Quasithin.H13.L32N1449Inputs
public import Certificates.Kernel.H13.Q1449Inv
import Certificates.Kernel.H13.ElemsO3
import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.Quasithin.H13.Q1449Cert
  CFSG.KC.Mat8P

theorem noCommP_cons (A X : ℕ) (O : List ℕ) :
    noCommP (A :: O) X = (!(Nat.beq (mulP A X) (mulP X A)) && noCommP O X) := rfl

theorem noCommP_mem {O : List ℕ} {X : ℕ} (h : noCommP O X = true) :
    ∀ A ∈ O, Nat.beq (mulP A X) (mulP X A) = false := by
  induction O with
  | nil => simp
  | cons A O ih =>
    rw [noCommP_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact h.1
    · exact ih h.2 B hB

theorem invsP_cons (Y : ℕ) (G : List ℕ) : invsP (Y :: G) =
    bif !(Nat.beq Y oneP) && Nat.beq (mulP Y Y) oneP then Y :: invsP G else invsP G := rfl

theorem mem_invsP {G : List ℕ} {X : ℕ} (hX : X ∈ G) (h1 : X ≠ oneP) (h2 : mulP X X = oneP) :
    X ∈ invsP G := by
  induction G with
  | nil => simp at hX
  | cons Y G ih =>
    rw [invsP_cons]
    rcases List.mem_cons.mp hX with rfl | hX
    · have e1 : Nat.beq X oneP = false := by
        cases h : Nat.beq X oneP
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h1
      rw [e1, h2, Nat.beq_refl, Bool.not_false, Bool.and_true, cond_true]
      exact List.mem_cons_self
    · cases (!(Nat.beq Y oneP) && Nat.beq (mulP Y Y) oneP)
      · exact ih hX
      · exact List.mem_cons_of_mem _ (ih hX)

theorem invRk_of (G I O : List ℕ) (hI : invsP G = I) (hO : (I.all fun X => invOK O X) = true) :
    ((G.map unpackM).all fun x => x == one8 || !(mul8 x x == one8) || small64B x ||
      fullAltB x || (O.map unpackM).all fun a => !(mul8 a x == mul8 x a)) = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
  by_cases h1 : unpackM X = one8
  · rw [h1, beq_self_eq_true, Bool.true_or, Bool.true_or, Bool.true_or, Bool.true_or]
  by_cases h2 : mul8 (unpackM X) (unpackM X) = one8
  swap
  · rw [beq_eq_false_iff_ne.mpr h2, Bool.not_false, Bool.or_true, Bool.true_or, Bool.true_or,
      Bool.true_or]
  have hX1 : X ≠ oneP := fun e => h1 (by rw [e, oneP_eq])
  have hX2 : mulP X X = oneP :=
    unpackM_inj (mulP_lt X X) oneP_lt (by rw [← mul8_unpackM, h2, oneP_eq])
  have hXI : X ∈ I := hI ▸ mem_invsP hX hX1 hX2
  have hok := List.all_eq_true.mp hO X hXI
  rw [invOK, Bool.or_eq_true, Bool.or_eq_true] at hok
  rcases hok with (hc | hs) | hf
  · have hall : ((O.map unpackM).all fun a => !(mul8 a (unpackM X) == mul8 (unpackM X) a)) =
        true := by
      rw [List.all_eq_true]
      intro a ha
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp ha
      rw [mul8_unpackM, mul8_unpackM, unpackM_beq (mulP_lt A X) (mulP_lt X A), Bool.not_eq_true',
        beq_eq_false_iff_ne]
      exact Nat.ne_of_beq_eq_false (noCommP_mem hc A hA)
    rw [hall, Bool.or_true]
  · rw [hs, Bool.or_true, Bool.true_or, Bool.true_or]
  · rw [hf, Bool.or_true, Bool.true_or]

theorem all_take_drop {f : ℕ → Bool} (n : ℕ) {I : List ℕ} (h1 : (I.take n).all f = true)
    (h2 : (I.drop n).all f = true) : I.all f = true := by
  rw [← List.take_append_drop n I, List.all_append, h1, h2, Bool.and_true]

theorem invRkB_of (h0 : o5L 0 = D.o5L0.map unpackM) (h1 : o5L 1 = D.o5L1.map unpackM) :
    invRkB = true := by
  simp only [invRkB, List.all_cons, List.all_nil, Bool.and_true, h0, h1, gamE, h2E_eq, omNE_eq,
    ↓reduceIte, Nat.one_ne_zero, if_false]
  rw [invRk_of _ _ _ (eq_of_beq invsL0_beq) (all_take_drop 160 invOK0a invOK0b),
    invRk_of _ _ _ (eq_of_beq invsL1_beq) (all_take_drop 240 invOK1a invOK1b), Bool.and_self]

end CertificateChecks.KernelH13

end
