
module

public import Certificates.Kernel.Misc.Tits.JLam8073
public import CFSG.Certificates.Kernel.Misc.BfsWordSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.V

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN CertificateChecks.KernelMisc.TitsJT CFSG.KS.Bfs
open scoped commutatorElement

theorem E_sq : ∀ e ∈ Esub, e * e = 1 := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := el_surj (Esub_le he)
  obtain ⟨-, h1, -⟩ := test_spec (tst hi)
  exact (sq_iff hi).1 (h1 ((Pb_iff hi).2 he)).2.1

theorem jFB_jEB (i : Fin 512) : jFB i = jEB i := by
  refine Bool.eq_iff_iff.2 ?_
  rw [jFB_iff, jEB_iff]
  constructor
  · intro h
    rw [memE_iff (elF_mem i)]
    intro m hm
    exact (h _ (bm_mem hm)).symm
  · intro h e he
    exact Grp.commute_of_sq E_sq h he

theorem Pb_false {i : Fin 512} (h : jEB i = false) : Pb i = false := by
  cases e : Pb i
  · rfl
  · have := (jEB_iff i).2 ((Pb_iff i.2).1 e)
    rw [h] at this
    exact absurd this (by decide)

theorem jEB_false {i : Fin 512} (h : Pb i = false) : jEB i = false := by
  cases e : jEB i
  · rfl
  · have := (Pb_iff i.2).2 ((jEB_iff i).1 e)
    rw [h] at this
    exact absurd this (by decide)

theorem vA : VCondsA jOps jEB jFB := ⟨jEB_eq, jFB_eq⟩

theorem vB : VCondsB jOps jEB jFB := by
  have hm : ∀ i j : Fin 512, jEB i = true → jEB j = true → jEB (jOps.mul i j) = true :=
    fun i j hi hj => by
      rw [jEB_iff, el_mulF]
      exact Esub.mul_mem ((jEB_iff i).1 hi) ((jEB_iff j).1 hj)
  have hv : ∀ i : Fin 512, jEB i = true → jEB (jOps.inv i) = true := fun i hi => by
    rw [jEB_iff, el_invF]
    exact Esub.inv_mem ((jEB_iff i).1 hi)
  have h1 : jEB jOps.one = true := by
    rw [jEB_iff, el_oneF]
    exact Esub.one_mem
  refine ⟨hm, hv, h1, ?_, ?_, ?_⟩ <;> simp only [jFB_jEB]
  exacts [hm, hv, h1]

theorem cls_one {i : ℕ} (h : Nat.beq (cls i) 1 = true) : memN i INV = true := by
  unfold cls at h
  revert h
  generalize memN i EIX = a
  generalize memN i INV = b
  cases a <;> cases b <;> decide

theorem card_E : (Finset.univ.filter fun i : Fin 512 => jEB i = true).card = 32 := by
  have hc : (Finset.univ.filter fun i : Fin 512 => jEB i = true) =
      Finset.univ.filter fun i : Fin 512 => Nat.beq (cls i) 0 = true := by
    refine Finset.filter_congr fun i _ => ?_
    rw [jEB_iff, ← Pb_iff i.2, Pb_cls i.2]
  rw [hc]
  decide +kernel

theorem iff_key (P Q : Prop) : (((P ↔ Q) ↔ P) ↔ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem vC : VCondsC jOps jEB jFB := by
  have hF : (Finset.univ.filter fun i : Fin 512 => jFB i = true) =
      Finset.univ.filter fun i : Fin 512 => jEB i = true :=
    Finset.filter_congr fun i _ => by rw [jFB_jEB]
  refine ⟨fun e he => ?_, fun e e' he he' => ?_, ?_, ?_, fun e he hc => ?_, fun i j => ?_⟩
  · exact elF_inj (by rw [el_mulF, el_oneF]; exact E_sq _ ((jEB_iff e).1 he))
  · exact elF_inj (by
      rw [el_mulF, el_mulF]
      exact (Grp.commute_of_sq E_sq ((jEB_iff e).1 he) ((jEB_iff e').1 he')).eq)
  · rw [hF, card_E]
  · rw [hF, card_E]
    norm_num
  · have hP := (Pb_iff e.2).2 ((jEB_iff e).1 he)
    obtain ⟨-, h1, -⟩ := test_spec (tst e.2)
    have hac : allc e = true := (allc_iff e.2).2 fun k hk => by
      obtain ⟨j, hj⟩ := elF_surj (sJ_mem hk)
      rw [← hj]
      have := hc j
      unfold Commute SemiconjBy
      rw [← el_mulF, ← el_mulF, this]
    rcases (h1 hP).2.2.2 hac with h | h
    · left
      exact elF_inj (by rw [el_oneF]; exact (one_iff e.2).1 h)
    · right
      exact elF_inj (by rw [el_zF]; exact (z_iff e.2).1 h)
  · rw [jFB_jEB, jEB_iff, el_commF, commutatorElement_def]
    have hx := elF_mem i
    have hy := elF_mem j
    have hJ := memE_iff (x := el i * el j * (el i)⁻¹ * (el j)⁻¹)
      (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy))
    rw [hJ]
    intro m hm
    have hb := bm_mem hm
    rw [Grp.comm_mul_iff zFacts.1 zFacts.2.1 zFacts.2.2 hb
        (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
      Grp.comm_mul_iff zFacts.1 zFacts.2.1 zFacts.2.2 hb (mul_mem hx hy) (inv_mem hx),
      Grp.comm_mul_iff zFacts.1 zFacts.2.1 zFacts.2.2 hb hx hy, Commute.inv_right_iff,
      Commute.inv_right_iff]
    exact iff_key _ _

theorem vD : VCondsD jOps jEB jCc := by
  intro i hi
  obtain ⟨-, -, h2⟩ := test_spec (tst i.2)
  obtain ⟨-, -, -, hcov, -⟩ := h2 (Pb_false hi)
  rw [List.all_eq_true]
  intro z _
  rw [List.any_eq_true]
  have hz := (memN_iff _ _).1 (test_spec (tst z.2)).1
  have hv := (memN_iff _ _).1 ((allL_iff' _ _).1 hcov _ hz)
  rw [← wordsOf_labels i, List.mem_map] at hv
  obtain ⟨w, hw, e⟩ := hv
  refine ⟨w, hw, ?_⟩
  rw [jEB_iff, ← lam0_zero_iff (Fin.is_lt _), lam0_mulF, lam0_invF, e, Nat.xor_self]

@[expose] noncomputable def gw : List ℕ → Equiv.Perm (Fin 1755)
  | [] => 1
  | k :: w => hGen k * gw w

theorem rG {k : ℕ} (hk : k < 3) : Rep 1755 (unpack 1755 11 (G k)) (hGen k) := by
  rw [← (hGenArr hk).1]
  exact (hGenArr hk).2

theorem rGI {k : ℕ} (hk : k < 3) : Rep 1755 (unpack 1755 11 (GI k)) (hGen k)⁻¹ := by
  obtain ⟨-, -, c3, -⟩ := canK_at (k := k) (by omega)
  exact rep_inv_of_isInvA (rG hk) (invEqK_sound (n := 1755) (w := 11) c3).2

theorem gw_norm : ∀ w : List ℕ, (∀ k ∈ w, k < 3) → ∀ x ∈ titsJ, gw w * x * (gw w)⁻¹ ∈ titsJ
  | [], _, x, hx => by simpa [gw] using hx
  | k :: w, hw, x, hx => by
    have e : gw (k :: w) * x * (gw (k :: w))⁻¹ = hGen k * (gw w * x * (gw w)⁻¹) * (hGen k)⁻¹ := by
      simp only [gw]
      group
    rw [e]
    exact hGen_norm (hw k List.mem_cons_self)
      (gw_norm w (fun k' h => hw k' (List.mem_cons_of_mem _ h)) x hx)

theorem wPt_eq : ∀ w : List ℕ, (∀ k ∈ w, k < 3) → ∀ p < 1755, wPt w p = (gw w (finPt 1755 p) : ℕ)
  | [], _, p, hp => by
    change p = _
    rw [gw, Equiv.Perm.one_apply, finPt_val hp]
  | k :: w, hw, p, hp => by
    have e : wPt (k :: w) p = pt (G k) (wPt w p) := rfl
    rw [e, wPt_eq w (fun k' h => hw k' (List.mem_cons_of_mem _ h)) p hp,
      pt_eq (rG (hw k List.mem_cons_self)) (Fin.is_lt _), finPt_coe, gw, Equiv.Perm.mul_apply]

theorem wIPt_eq : ∀ w : List ℕ, (∀ k ∈ w, k < 3) → ∀ p < 1755,
    wIPt w p = ((gw w)⁻¹ (finPt 1755 p) : ℕ)
  | [], _, p, hp => by
    change p = _
    rw [gw, inv_one, Equiv.Perm.one_apply, finPt_val hp]
  | k :: w, hw, p, hp => by
    have e : wIPt (k :: w) p = wIPt w (pt (GI k) p) := rfl
    rw [e, pt_eq (rGI (hw k List.mem_cons_self)) hp,
      wIPt_eq w (fun k' h => hw k' (List.mem_cons_of_mem _ h)) _ (Fin.is_lt _), finPt_coe, gw,
      mul_inv_rev, Equiv.Perm.mul_apply]

theorem wck_gen {a j : ℕ} (ha : a < 512) (hj : j < 512) {w : List ℕ} (hw : ∀ k ∈ w, k < 3) :
    onB (fun p => Nat.beq (wPt w (X a (wIPt w p))) (X j p)) = true ↔
      gw w * el a * (gw w)⁻¹ = el j :=
  onB_eq_iff (fa := fun p => wPt w (X a (wIPt w p))) (fb := fun p => X j p)
    (gw_norm w hw _ (el_mem ha)) (el_mem hj)
    (fun p hp => by
      rw [wIPt_eq w hw p hp, X_eq ha (Fin.is_lt _), finPt_coe, wPt_eq w hw _ (Fin.is_lt _),
        finPt_coe, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply])
    (fun p hp => X_eq hj hp)

theorem wck_iff {j : ℕ} (hj : j < 512) {w : List ℕ} (hw : ∀ k ∈ w, k < 3) :
    wck j w = true ↔ gw w * el 129 * (gw w)⁻¹ = el j :=
  wck_gen (a := 129) (by norm_num) hj hw

theorem wAll_spec : ∀ (L : List ℕ) (W : List (List ℕ)), wAll L W = true →
    ∀ j ∈ L, ∃ w ∈ W, wck j w = true
  | [], _, _, j, hj => absurd hj List.not_mem_nil
  | j0 :: L, [], h, _, _ => by
    have e : wAll (j0 :: L) [] = false := rfl
    rw [e] at h
    exact Bool.noConfusion h
  | j0 :: L, w :: W, h, j, hj => by
    have e : wAll (j0 :: L) (w :: W) =
        Bool.rec (motive := fun _ => Bool) false (wAll L W) (wck j0 w) := rfl
    rw [e] at h
    cases hc : wck j0 w
    · rw [hc] at h
      exact Bool.noConfusion h
    · rw [hc] at h
      rcases List.mem_cons.1 hj with rfl | hj'
      · exact ⟨w, List.mem_cons_self, hc⟩
      · obtain ⟨w', hw', e'⟩ := wAll_spec L W h j hj'
        exact ⟨w', List.mem_cons_of_mem _ hw', e'⟩

theorem WD_lt : ∀ w ∈ WD, ∀ k ∈ w, k < 3 := by decide +kernel

theorem walk_el : ∀ (L : List ℕ), (∀ k ∈ L, k < 3) → ∀ x < 512,
    Bfs.walkT jCjT L x < 512 ∧ el (Bfs.walkT jCjT L x) = gw L * el x * (gw L)⁻¹
  | [], _, x, hx => ⟨hx, by simp [Bfs.walkT, gw]⟩
  | k :: L, hL, x, hx => by
    obtain ⟨h1, h2⟩ := walk_el L (fun k' h => hL k' (List.mem_cons_of_mem _ h)) x hx
    have hk := hL k List.mem_cons_self
    obtain ⟨c1, c2⟩ := cjT hk h1
    refine ⟨c1, ?_⟩
    change el (jCjT[k]!)[Bfs.walkT jCjT L x]! = _
    rw [c2, h2]
    simp only [gw]
    group

theorem conjWord_walk : ∀ (L : List ℕ), (∀ k ∈ L, k < 3) → ∀ x : Fin 512,
    (conjWord jCj (L.map (finPt 3)) x : ℕ) = Bfs.walkT jCjT L x
  | [], _, x => rfl
  | k :: L, hL, x => by
    have hk := hL k List.mem_cons_self
    change (jCj (finPt 3 k) (conjWord jCj (L.map (finPt 3)) x) : ℕ) = (jCjT[k]!)[Bfs.walkT jCjT L x]!
    rw [cj_val, conjWord_walk L (fun k' h => hL k' (List.mem_cons_of_mem _ h)) x, finPt_val hk]

theorem xor_zero_eq {a b : ℕ} (h : a ^^^ b = 0) : a = b :=
  calc a = a ^^^ 0 := (Nat.xor_zero a).symm
    _ = a ^^^ (a ^^^ b) := by rw [h]
    _ = b := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem find_congr {p q : ℕ → Bool} : ∀ {L : List ℕ}, (∀ x ∈ L, p x = q x) → L.find? p = L.find? q
  | [], _ => rfl
  | a :: L, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      find_congr fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem sq_tab {i : ℕ} (hi : i < 512) : ((jMulT[i]!)[i]! == jOneI) = sq i := by
  refine Bool.eq_iff_iff.2 ?_
  rw [beq_iff_eq, sq_iff hi]
  obtain ⟨h1, h2⟩ := mulT hi hi
  constructor
  · intro e
    rw [← h2, e, oneT.2]
  · intro e
    exact el_inj h1 oneT.1 (by rw [h2, e, oneT.2])

theorem jI0N_eq : jI0N = 129 := by
  have h : ∀ i ∈ List.range 512,
      (!(jFBarr[i]!) && (jMulT[i]!)[i]! == jOneI) = Nat.beq (cls i) 1 := by
    intro i hi
    have hi' := List.mem_range.1 hi
    have eF : jFBarr[i]! = jEB ⟨i, hi'⟩ := jFB_jEB ⟨i, hi'⟩
    rw [eF, sq_tab hi']
    obtain ⟨-, h1, h2⟩ := test_spec (tst hi')
    cases hP : Pb i
    · rw [jEB_false (i := ⟨i, hi'⟩) hP, (h2 hP).2.2.2.2]
      rfl
    · have hE : jEB ⟨i, hi'⟩ = true := (jEB_iff ⟨i, hi'⟩).2 ((Pb_iff hi').1 hP)
      rw [hE]
      have c0 := Nat.eq_of_beq_eq_true (h1 hP).1
      rw [c0]
      rfl
  unfold jI0N
  rw [find_congr h]
  decide +kernel

theorem jI0_eq : jI0 = ⟨129, by norm_num⟩ := by
  unfold jI0
  rw [jI0N_eq]
  exact finPt_eq (by norm_num)

theorem jWordAux_eq (par gl : Array ℕ) :
    ∀ fuel j, jWordAux par gl fuel j = wordT 512 jI0N par gl fuel j
  | 0, _ => rfl
  | fuel + 1, j => by
    rw [jWordAux, wordT, jWordAux_eq par gl fuel]

theorem jBfs_eq : jBfs = bfsT 512 3 jI0N jCjT := rfl

theorem vE : VCondsE jOps jFB jCc jCj jI0 jWtab := by
  have h129 : (129 : ℕ) < 512 := by norm_num
  obtain ⟨-, -, h2⟩ := test_spec (tst h129)
  have hP : Pb 129 = false := by rw [Pb_cls h129]; decide
  have hs : sq 129 = true := by rw [← (h2 hP).2.2.2.2, ← Nat.beq_refl 1]; rfl
  refine ⟨⟨?_, ?_⟩, fun j hjF hj2 => ?_, fun i hi => ?_⟩
  · rw [jI0_eq, jFB_jEB]
    exact jEB_false hP
  · rw [jI0_eq]
    exact elF_inj (by rw [el_mulF, el_oneF]; exact (sq_iff h129).1 hs)
  · rw [jFB_jEB] at hjF
    have hPj := Pb_false hjF
    obtain ⟨-, -, k2⟩ := test_spec (tst j.2)
    have hsj : sq j = true := (sq_iff j.2).2 (by rw [← el_mulF, hj2, el_oneF])
    have hc : Nat.beq (cls j) 1 = true := by rw [(k2 hPj).2.2.2.2, hsj]
    have hinv := (memN_iff _ _).1 (cls_one hc)
    obtain ⟨w, hwW, hwc⟩ := wAll_spec INV WD wordsK j hinv
    have hw := WD_lt w hwW
    have hg := (wck_iff j.2 hw).1 hwc
    obtain ⟨wl, we⟩ := walk_el w hw 129 h129
    have hreach : Bfs.walkT jCjT w 129 = j := el_inj wl j.2 (by rw [we, hg])
    have hadj : ∀ k < 3, ∀ x < 512, (jCjT[k]!)[x]! < 512 := fun k hk x hx => (cjT hk hx).1
    obtain ⟨b1, b2⟩ := bfs_word_sound (n := 512) (m := 3) (fuel := 600) h129 (by norm_num) hadj
      hw hreach
    refine Fin.ext ?_
    unfold jWtab
    rw [jWordAux_eq, jBfs_eq, jI0N_eq, jI0_eq, conjWord_walk _ b1]
    exact b2
  · rw [jFB_jEB] at hi ⊢
    obtain ⟨-, -, k2⟩ := test_spec (tst i.2)
    have h4 := (k2 (Pb_false hi)).2.2.1
    refine jEB_false ?_
    cases e : Pb (jOps.mul (jCc i) (jOps.inv i))
    · rfl
    · have h0 := (Pb_lam (Fin.is_lt _)).1 e
      rw [lam0_mulF, lam0_invF] at h0
      replace h0 := xor_zero_eq h0
      have h1 := lam0_iter (k := 1) (j := 4) (by norm_num) (by norm_num) (by norm_num) i
      rw [Function.iterate_one] at h1
      rw [h1] at h0
      rw [h0, Nat.beq_refl] at h4
      exact absurd h4 (by decide)

theorem vconds : VConds jOps jEB jFB jCc jCj jI0 jWtab := ⟨vA, vB, vC, vD, vE⟩

end CertificateChecks.KernelMisc.TitsJT.V

end
