module

public import Certificates.Kernel.Fi22F.ThreeChecks
public import Certificates.Kernel.Fi22.Model

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC CFSG.KC.Fi22F.Three CFSG.KC.Fi22B.Cov CFSG.Certificates.Fi22Kill
  CFSG.Sporadic.Presentation.Fi22Exact CertificateChecks.KernelFi22

abbrev FG : Type := CFSG.CosetTable.PG 6 wsF

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem toGroup_mk {α G : Type*} [Group G] {f : α → G} {rels : Set (FreeGroup α)}
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (u : FreeGroup α) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels u) = FreeGroup.lift f u := by
  have h' : (PresentedGroup.toGroup h).comp (PresentedGroup.mk rels) = FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro a
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of h
  exact DFunLike.congr_fun h' u

theorem lift_sign_mk {m : ℕ} (u : List (Fin m × Bool)) :
    FreeGroup.lift (fun _ : Fin m => Multiplicative.ofAdd (1 : ZMod 2)) (FreeGroup.mk u) =
      Multiplicative.ofAdd (u.length : ZMod 2) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    obtain ⟨i, b⟩ := x
    have h : FreeGroup.mk ((i, b) :: u) = FreeGroup.mk [(i, b)] * FreeGroup.mk u := rfl
    rw [h, map_mul, ih]
    cases b
    · have h1 : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
      rw [h1, map_inv, FreeGroup.lift_apply_of, List.length_cons, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      push_cast
      have : (-1 : ZMod 2) = 1 := by decide
      rw [this, add_comm]
    · have h1 : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
      rw [h1, FreeGroup.lift_apply_of, List.length_cons, ← ofAdd_add]
      congr 1
      push_cast
      rw [add_comm]

theorem xf_wf (i : Fin 6) : wf4 (XF i.val) = true ∧ Nat.beq (mul4 (XF i.val) (XF i.val)) one4 = true := by
  have h := xf_ok
  simp only [xfOK, xfOne, andB, Bool.and_eq_true] at h
  have e : ∀ x y : Bool, Bool.rec false y x = (x && y) := by intro x y; cases x <;> rfl
  simp only [e, Bool.and_eq_true] at h
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩⟩ := h
  fin_cases i
  exacts [⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩]

theorem evalL_dec (w : List (Fin 6 × Bool)) :
    wf4 (evalL w) = true ∧ dec4 (evalL w) = (w.map fun p => dec4 (XF p.1.val)).prod := by
  induction w with
  | nil => exact ⟨wf4_one, dec4_one⟩
  | cons p w ih =>
    change wf4 (CFSG.KC.Loop.strictN (evalL w) _) = true ∧ dec4 (CFSG.KC.Loop.strictN (evalL w) _) = _
    rw [strictN_eq']
    obtain ⟨m1, m2⟩ := mul4_sound (xf_wf p.1).1 ih.1
    refine ⟨m1, ?_⟩
    rw [m2, ih.2, List.map_cons, List.prod_cons]

theorem pw4_zero (X : ℕ) : pw4 X 0 = one4 := rfl

theorem pw4_succ (X k : ℕ) : pw4 X (k + 1) = CFSG.KC.Loop.strictN (pw4 X k) (fun a => mul4 a X) := rfl

theorem evalL_cons (p : Fin 6 × Bool) (w : List (Fin 6 × Bool)) :
    evalL (p :: w) = CFSG.KC.Loop.strictN (evalL w) (fun x => mul4 (XF p.1.val) x) := rfl

theorem evalL_nil : evalL [] = one4 := rfl

theorem pw4_dec {X : ℕ} (hX : wf4 X = true) (k : ℕ) : wf4 (pw4 X k) = true ∧ dec4 (pw4 X k) = dec4 X ^ k := by
  induction k with
  | zero =>
    rw [pw4_zero, pow_zero]
    exact ⟨wf4_one, dec4_one⟩
  | succ k ih =>
    rw [pw4_succ, strictN_eq']
    obtain ⟨m1, m2⟩ := mul4_sound ih.1 hX
    exact ⟨m1, by rw [m2, ih.2]; exact (pow_succ (dec4 X) k).symm⟩

@[expose] noncomputable def uF (i : Fin 6) : GL4 := unit4 (XF i.val) (xf_wf i).1 (xf_wf i).2

theorem uF_inv (i : Fin 6) : (uF i)⁻¹ = uF i := Units.ext rfl

theorem lift_uF (w : List (Fin 6 × Bool)) :
    ((FreeGroup.lift uF (FreeGroup.mk w) : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (evalL w) := by
  rw [(evalL_dec w).2, FreeGroup.lift_mk, ← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨i, b⟩ _
  cases b
  · simp only [Function.comp_apply, Units.coeHom_apply, cond_false, uF_inv]
    rfl
  · rfl

theorem allOne_mem {ws : List (List (Fin 6 × Bool))} (h : allOne ws = true) :
    ∀ w ∈ ws, evalL w = one4 := by
  induction ws with
  | nil => intro w hw; cases hw
  | cons v ws ih =>
    have h' : andB (Nat.beq (evalL v) one4) (allOne ws) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Nat.eq_of_beq_eq_true h1
    · exact ih h2 w hw

noncomputable def psiF : FG →* GL4 :=
  PresentedGroup.toGroup (f := uF) (by
    intro r hr
    simp only [Set.mem_setOf_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    apply Units.ext
    rw [lift_uF, allOne_mem rels_ok w hw, Units.val_one, dec4_one])

theorem psiF_mk (w : List (Fin 6 × Bool)) :
    ((psiF (PresentedGroup.mk _ (FreeGroup.mk w)) : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (evalL w) := by
  unfold psiF
  rw [toGroup_mk, lift_uF]

theorem mk_flatten_replicate (n : ℕ) (w : List (Fin 6 × Bool)) :
    (FreeGroup.mk (List.replicate n w).flatten : FreeGroup (Fin 6)) = FreeGroup.mk w ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

noncomputable abbrev g1F : FG := PresentedGroup.mk _ (FreeGroup.mk g1w)

theorem three_dvd_orderOf_g1 : 3 ∣ orderOf g1F := by
  have hw := (evalL_dec Pw).1
  obtain ⟨hS, hSd⟩ := pw4_dec hw 91
  have e : (FreeGroup.mk g1w : FreeGroup (Fin 6)) = FreeGroup.mk Pw ^ 91 := by
    unfold g1w
    exact mk_flatten_replicate 91 Pw
  have hg : psiF g1F = psiF (PresentedGroup.mk _ (FreeGroup.mk Pw)) ^ 91 := by
    rw [g1F, e, map_pow, map_pow]
  have hval : ((psiF g1F : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (pw4 (evalL Pw) 91) := by
    rw [hg, Units.val_pow_eq_pow_val, psiF_mk, hSd]
  have h := g1_ok
  unfold g1OK ord3 at h
  obtain ⟨h3, hne⟩ := andB_true h
  have hne : Nat.beq (pw4 (evalL Pw) 91) one4 = false := by
    revert hne
    cases Nat.beq (pw4 (evalL Pw) 91) one4 <;> simp [notB]
  have h3' : psiF g1F ^ 3 = 1 := by
    apply Units.ext
    have e3 : ∀ M : Matrix (Fin 27) (Fin 27) F4, M ^ 3 = M * M * M := fun M => by
      rw [pow_succ M 2, pow_two M]
    rw [Units.val_pow_eq_pow_val, hval, Units.val_one, e3,
      ← (mul4_sound hS hS).2, ← (mul4_sound (mul4_sound hS hS).1 hS).2, Nat.eq_of_beq_eq_true h3, dec4_one]
  have hne' : psiF g1F ≠ 1 := by
    intro e
    have e2 := congrArg (fun u : GL4 => (u : Matrix (Fin 27) (Fin 27) F4)) e
    change ((psiF g1F : GL4) : Matrix (Fin 27) (Fin 27) F4) = 1 at e2
    rw [hval, ← dec4_one] at e2
    have := dec4_inj hS wf4_one e2
    rw [this, Nat.beq_refl] at hne
    exact Bool.noConfusion hne
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (psiF g1F) = 3 := orderOf_eq_prime h3' hne'
  rw [← ho]
  exact orderOf_map_dvd psiF g1F

theorem even_rels : wsF.all (fun w => w.length % 2 == 0) = true := by decide +kernel

theorem len_g1 : g1w.length = 11011 := by decide +kernel

noncomputable def sgnF : FG →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := fun _ : Fin 6 => Multiplicative.ofAdd (1 : ZMod 2)) (by
    intro r hr
    simp only [Set.mem_setOf_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_sign_mk]
    have h := (List.all_eq_true.mp even_rels) w hw
    simp only [beq_iff_eq] at h
    have : (w.length : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      omega
    rw [this]
    rfl)

theorem two_dvd_orderOf_g1 : 2 ∣ orderOf g1F := by
  have hs : sgnF g1F = Multiplicative.ofAdd (1 : ZMod 2) := by
    unfold sgnF
    rw [toGroup_mk, lift_sign_mk, len_g1]
    rfl
  have ho : orderOf (sgnF g1F) = 2 := by
    rw [hs]
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)
  rw [← ho]
  exact orderOf_map_dvd sgnF g1F

theorem six_dvd_orderOf_g1 : 6 ∣ orderOf g1F :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) two_dvd_orderOf_g1 three_dvd_orderOf_g1

end CertificateChecks.KernelFi22F

end
