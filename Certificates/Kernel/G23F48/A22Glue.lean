module

public import Certificates.Kernel.G23F48.A22Check
public import Certificates.Kernel.G23F48.ChainsGlue
public import Certificates.Kernel.G23F48.OrbitGlue
public import CFSG.Certificates.Kernel.G23F48.Orders

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KD.G23A22
open CFSG.Sporadic.HNOddCore (arrGen)
open MulAction

theorem onPermOfArr_eq {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.ONSchreier.PRep n t g) : CFSG.ONSchreier.permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · rw [h.apply hi]
      exact (g _).2
    · rw [h.apply hi, h.apply hj] at hij
      exact congrArg Fin.val (g.injective (Fin.ext hij))
  have ht : CFSG.ONSchreier.PRep n t (CFSG.ONSchreier.permOfArr n t) := fun x => by
    rw [CFSG.ONSchreier.permOfArr, dite_eq_left hc]
    rfl
  exact ht.unique h

theorem oprep_unique {n w P : ℕ} {g h : Equiv.Perm (Fin n)} (hg : Orb.PRep n w P g)
    (hh : Orb.PRep n w P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_of_bind {t : Array ℕ} {P Q : ℕ} (hb : arrBind t 728 10 P = true)
    (hp : permOK 728 10 (mask 10) (728 * 10) P Q = true) :
    CFSG.ONSchreier.PRep 728 t (CFSG.ONSchreier.permOfArr 728 t) ∧
      Orb.PRep 728 10 P (CFSG.ONSchreier.permOfArr 728 t) ∧
      Orb.PRep 728 10 Q (CFSG.ONSchreier.permOfArr 728 t)⁻¹ := by
  obtain ⟨g, hg, hgi⟩ := CFSG.KC.EnumSound.permOK_perm hp
  have ht : CFSG.ONSchreier.PRep 728 t g := fun x => by
    rw [arrBind_sound hb, Orb.unpack_get x.2]
    exact hg x
  rw [onPermOfArr_eq ht]
  exact ⟨ht, hg, hgi⟩

@[expose] noncomputable def gam (i : ℕ) : Equiv.Perm (Fin 728) :=
  CFSG.ONSchreier.permOfArr 728 (burnsideF48t_g23Gens ())[i]!

@[expose] noncomputable def sig (i : ℕ) : Equiv.Perm (Fin 728) :=
  CFSG.ONSchreier.permOfArr 728 burnsideF48t_g23LArr[i]!

@[expose] noncomputable def tau : Equiv.Perm (Fin 728) :=
  CFSG.ONSchreier.permOfArr 728 burnsideF48t_g23Tau

theorem prep_gen {i : ℕ} (hi : i < 4) :
    CFSG.ONSchreier.PRep 728 (burnsideF48t_g23Gens ())[i]! (gam i) ∧
      Orb.PRep 728 10 (GP i) (gam i) ∧ Orb.PRep 728 10 (GPI i) (gam i)⁻¹ :=
  prep_of_bind (allN_spec g_bind i hi) (allN_spec g_perm i hi)

theorem prep_letter {i : ℕ} (hi : i < 4) :
    CFSG.ONSchreier.PRep 728 burnsideF48t_g23LArr[i]! (sig i) ∧
      Orb.PRep 728 10 (LP i) (sig i) ∧ Orb.PRep 728 10 (LPI i) (sig i)⁻¹ :=
  prep_of_bind (allN_spec l_bind i hi) (allN_spec l_perm i hi)

theorem prep_tau : CFSG.ONSchreier.PRep 728 burnsideF48t_g23Tau tau ∧
    Orb.PRep 728 10 (TP 0) tau ∧ Orb.PRep 728 10 (TP 1) tau⁻¹ :=
  prep_of_bind t_bind t_perm

theorem recL : burnsideF48t_RecL 728 burnsideF48t_g23LArr (burnsideF48t_g23LInv ())
    (fun i : Fin 4 => sig i) := fun i => by
  have h := (prep_letter i.2).1
  refine ⟨h, ?_⟩
  have e : (burnsideF48t_g23LInv ())[(i : ℕ)]! =
      CFSG.ONSchreier.Native.pinvCand 728 burnsideF48t_g23LArr[(i : ℕ)]! := by
    have hs : (i : ℕ) < burnsideF48t_g23LArr.size := i.2.trans_eq rfl
    rw [burnsideF48t_g23LInv, getElem!_pos _ _ (by simpa only [Array.size_map] using hs),
      getElem!_pos burnsideF48t_g23LArr _ hs, Array.getElem_map]
  rw [e]
  exact (CFSG.KS.BfsPar.prep_pinvCand h).1

@[expose] noncomputable def wv {n : ℕ} (σ : ℕ → Equiv.Perm (Fin n)) :
    List (ℕ × Bool) → Equiv.Perm (Fin n)
  | [] => 1
  | l :: w => (if l.2 then σ l.1 else (σ l.1)⁻¹) * wv σ w

theorem prep_evPN {n w k : ℕ} {LP LPI : ℕ → ℕ} {σ : ℕ → Equiv.Perm (Fin n)}
    (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hσ : ∀ i < k, Orb.PRep n w (LP i) (σ i) ∧ Orb.PRep n w (LPI i) (σ i)⁻¹) :
    ∀ word : List (ℕ × Bool), (∀ l ∈ word, l.1 < k) →
      Orb.PRep n w (evPN n w LP LPI word) (wv σ word)
  | [], _ => Orb.prep_pidn hn hw
  | ⟨i, b⟩ :: word, hl => by
    have hi : i < k := hl _ List.mem_cons_self
    have ih := prep_evPN hn hw hσ word fun l h => hl l (List.mem_cons_of_mem _ h)
    cases b
    · exact Orb.prep_pcomp (by omega) (hσ i hi).2 ih
    · exact Orb.prep_pcomp (by omega) (hσ i hi).1 ih

theorem wv_mem {n : ℕ} {σ : ℕ → Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))} {k : ℕ}
    (hσ : ∀ i < k, σ i ∈ H) : ∀ word : List (ℕ × Bool), (∀ l ∈ word, l.1 < k) → wv σ word ∈ H
  | [], _ => H.one_mem
  | ⟨i, b⟩ :: word, hl => by
    have hi : i < k := hl _ List.mem_cons_self
    have ih := wv_mem hσ word fun l h => hl l (List.mem_cons_of_mem _ h)
    cases b
    · exact H.mul_mem (H.inv_mem (hσ i hi)) ih
    · exact H.mul_mem (hσ i hi) ih

theorem wX_letters : (wX.all fun w => w.all fun l => Nat.blt l.1 4) = true := by
  decide +kernel

theorem wX_lt {i : ℕ} : ∀ l ∈ wX.getD i [], l.1 < 4 := by
  intro l hl
  have h := List.all_eq_true.1 wX_letters
  by_cases hi : i < wX.length
  · rw [List.getD_eq_getElem _ _ hi] at hl
    have := List.all_eq_true.1 (h _ (List.getElem_mem hi)) l hl
    simpa using this
  · rw [List.getD_eq_default _ _ (by omega)] at hl
    simp at hl

theorem gam_mem {i : ℕ} (hi : i < 4) : gam i ∈ arrGen 728 (burnsideF48t_g23Gens ()) :=
  Subgroup.subset_closure ⟨i, hi.trans_eq rfl,
    CFSG.Sporadic.HNOddCore.permOfArr_eq_of_prep (prep_gen hi).1⟩

theorem wv_wX_mem (i : ℕ) : wv gam (wX.getD i []) ∈ arrGen 728 (burnsideF48t_g23Gens ()) :=
  wv_mem (fun _ hj => gam_mem hj) _ wX_lt

theorem letter_mem {i : ℕ} (hi : i < 4) : sig i ∈ arrGen 728 (burnsideF48t_g23Gens ()) := by
  have hw := prep_evPN (k := 4) (by norm_num) (by norm_num)
    (fun j hj => (prep_gen hj).2) (wX.getD i []) wX_lt
  rw [Nat.eq_of_beq_eq_true (allN_spec x_words.1 i hi)] at hw
  rw [oprep_unique (prep_letter hi).2.1 hw]
  exact wv_wX_mem i

theorem tau_conj_mem {i : ℕ} (hi : i < 4) :
    tau * gam i * tau⁻¹ ∈ arrGen 728 (burnsideF48t_g23Gens ()) := by
  have hw := prep_evPN (k := 4) (by norm_num) (by norm_num)
    (fun j hj => (prep_gen hj).2) (wX.getD (i + 4) []) wX_lt
  rw [Nat.eq_of_beq_eq_true (allN_spec x_words.2 i hi)] at hw
  have hc : Orb.PRep 728 10 (pconj 728 10 (TP 0) (TP 1) (GP i)) (tau * gam i * tau⁻¹) :=
    Orb.prep_pcomp (by norm_num) (Orb.prep_pcomp (by norm_num) prep_tau.2.1 (prep_gen hi).2.1)
      prep_tau.2.2
  rw [oprep_unique hc hw]
  exact wv_wX_mem (i + 4)

theorem sig_apply {i : ℕ} (hi : i < 4) (p : Fin 728) :
    ((sig i p : Fin 728) : ℕ) = pg 10 (mask 10) (LP i) p :=
  ((prep_letter hi).2.1 p).symm

theorem sig_fix {i : ℕ} (hi : i < 4) {x : Fin 728} (h : pg 10 (mask 10) (LP i) x = x) :
    sig i ∈ stabilizer (Equiv.Perm (Fin 728)) x := by
  rw [mem_stabilizer_iff, Equiv.Perm.smul_def]
  exact Fin.ext ((sig_apply hi x).trans h)

theorem arrGen_letters_le {O : Array (Array ℕ)} {H : Subgroup (Equiv.Perm (Fin 728))}
    (idx : ℕ → ℕ)
    (hO : ∀ k < O.size, idx k < 4 ∧ O[k]! = burnsideF48t_g23LArr[idx k]! ∧ sig (idx k) ∈ H) :
    arrGen 728 O ≤ H := by
  rw [arrGen, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨hi, he, hm⟩ := hO k hk
  rw [he, CFSG.Sporadic.HNOddCore.permOfArr_eq_of_prep (prep_letter hi).1]
  exact hm

theorem sig_mem_arrGen {O : Array (Array ℕ)} {k i : ℕ} (hk : k < O.size)
    (he : O[k]! = burnsideF48t_g23LArr[i]!) (hi : i < 4) : sig i ∈ arrGen 728 O :=
  Subgroup.subset_closure ⟨k, hk, by
    rw [he, CFSG.Sporadic.HNOddCore.permOfArr_eq_of_prep (prep_letter hi).1]⟩

theorem sig_mem_X_fix {i : ℕ} (hi : i < 4) {x : Fin 728} (h : pg 10 (mask 10) (LP i) x = x) :
    sig i ∈ arrGen 728 (burnsideF48t_g23Gens ()) ⊓ stabilizer (Equiv.Perm (Fin 728)) x :=
  Subgroup.mem_inf.2 ⟨letter_mem hi, sig_fix hi h⟩

theorem P1_le : arrGen 728 burnsideF48t_g23P1Arr ≤
    arrGen 728 (burnsideF48t_g23Gens ()) ⊓ stabilizer (Equiv.Perm (Fin 728)) (0 : Fin 728) := by
  obtain ⟨f1, -, f3, -, f5, -⟩ := fix_ok
  refine arrGen_letters_le id fun k hk => ?_
  have hk3 : k < 3 := hk
  interval_cases k
  · exact ⟨by norm_num, rfl, sig_mem_X_fix (by norm_num) f1⟩
  · exact ⟨by norm_num, rfl, sig_mem_X_fix (by norm_num) f3⟩
  · exact ⟨by norm_num, rfl, sig_mem_X_fix (by norm_num) f5⟩

theorem P2_le : arrGen 728 burnsideF48t_g23P2Arr ≤
    arrGen 728 (burnsideF48t_g23Gens ()) ⊓ stabilizer (Equiv.Perm (Fin 728)) (364 : Fin 728) := by
  obtain ⟨-, f2, -, f4, -, f6, -⟩ := fix_ok
  refine arrGen_letters_le (fun k => k + k / 2) fun k hk => ?_
  have hk3 : k < 3 := hk
  interval_cases k
  · exact ⟨by norm_num, rfl, sig_mem_X_fix (by norm_num) f2⟩
  · exact ⟨by norm_num, rfl, sig_mem_X_fix (by norm_num) f4⟩
  · exact ⟨by norm_num, rfl, sig_mem_X_fix (by norm_num) f6⟩

theorem B_le_P1 : arrGen 728 burnsideF48t_g23BArr ≤
    arrGen 728 burnsideF48t_g23P1Arr ⊓ stabilizer (Equiv.Perm (Fin 728)) (364 : Fin 728) := by
  obtain ⟨-, f2, -, f4, -⟩ := fix_ok
  refine arrGen_letters_le id fun k hk => ?_
  have hk2 : k < 2 := hk
  interval_cases k
  · exact ⟨by norm_num, rfl, Subgroup.mem_inf.2 ⟨sig_mem_arrGen (k := 0) (by decide) rfl
      (by norm_num), sig_fix (by norm_num) f2⟩⟩
  · exact ⟨by norm_num, rfl, Subgroup.mem_inf.2 ⟨sig_mem_arrGen (k := 1) (by decide) rfl
      (by norm_num), sig_fix (by norm_num) f4⟩⟩

theorem B_le_P2 : arrGen 728 burnsideF48t_g23BArr ≤
    arrGen 728 burnsideF48t_g23P2Arr ⊓ stabilizer (Equiv.Perm (Fin 728)) (0 : Fin 728) := by
  obtain ⟨f1, -, f3, -⟩ := fix_ok
  refine arrGen_letters_le id fun k hk => ?_
  have hk2 : k < 2 := hk
  interval_cases k
  · exact ⟨by norm_num, rfl, Subgroup.mem_inf.2 ⟨sig_mem_arrGen (k := 0) (by decide) rfl
      (by norm_num), sig_fix (by norm_num) f1⟩⟩
  · exact ⟨by norm_num, rfl, Subgroup.mem_inf.2 ⟨sig_mem_arrGen (k := 1) (by decide) rfl
      (by norm_num), sig_fix (by norm_num) f3⟩⟩

theorem card_P1_P2_B (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696) :
    Nat.card (arrGen 728 burnsideF48t_g23P1Arr) = 11664 ∧
      Nat.card (arrGen 728 burnsideF48t_g23P2Arr) = 11664 ∧
      Nat.card (arrGen 728 burnsideF48t_g23BArr) = 2916 := by
  have hγ : ∀ s < 4, CFSG.ONSchreier.PRep 728 (burnsideF48t_g23Gens ())[s]! (gam s) ∧
      gam s ∈ arrGen 728 (burnsideF48t_g23Gens ()) := fun s hs => ⟨(prep_gen hs).1, gam_mem hs⟩
  obtain ⟨Op, hOp, hOpX⟩ := orbit_X_0 hγ
  obtain ⟨Oq, hOq, hOqX⟩ := orbit_X_364 hγ
  obtain ⟨O₁, hO₁, hO₁P⟩ := orbit_P1 (σ := sig) (H := arrGen 728 burnsideF48t_g23P1Arr)
    fun s hs => by
      interval_cases s
      · exact ⟨(prep_letter (i := 0) (by norm_num)).1, sig_mem_arrGen (k := 0) (by decide) rfl
          (by norm_num)⟩
      · exact ⟨(prep_letter (i := 1) (by norm_num)).1, sig_mem_arrGen (k := 1) (by decide) rfl
          (by norm_num)⟩
      · exact ⟨(prep_letter (i := 2) (by norm_num)).1, sig_mem_arrGen (k := 2) (by decide) rfl
          (by norm_num)⟩
  obtain ⟨O₂, hO₂, hO₂P⟩ := orbit_P2 (σ := fun s => sig (s + s / 2))
    (H := arrGen 728 burnsideF48t_g23P2Arr) fun s hs => by
      interval_cases s
      · exact ⟨(prep_letter (i := 0) (by norm_num)).1, sig_mem_arrGen (k := 0) (by decide) rfl
          (by norm_num)⟩
      · exact ⟨(prep_letter (i := 1) (by norm_num)).1, sig_mem_arrGen (k := 1) (by decide) rfl
          (by norm_num)⟩
      · exact ⟨(prep_letter (i := 3) (by norm_num)).1, sig_mem_arrGen (k := 2) (by decide) rfl
          (by norm_num)⟩
  have hab : sig 0 ∈ arrGen 728 burnsideF48t_g23BArr ∧ sig 1 ∈ arrGen 728 burnsideF48t_g23BArr :=
    ⟨sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num),
      sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num)⟩
  exact card_parabolics_of_orbits hX hOp hOpX hOq hOqX hO₁ hO₁P hO₂ hO₂P P1_le P2_le B_le_P1
    B_le_P2 (S0_le recL hab) (K_le recL hab) card_S0 card_K

end CFSG.KC.G23F48

end
