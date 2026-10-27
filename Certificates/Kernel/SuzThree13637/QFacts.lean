
module

public import Certificates.Kernel.SuzThree13637.QChk
public import Certificates.Kernel.SuzThree13637.HypFacts
public import Certificates.Kernel.SuzThree13637.CFacts
public import CFSG.Certificates.Kernel.Spor.QMdlKSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PSearch CFSG.KS.HypK CFSG.KS.QMdlK
  CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.RankThree.Native
open CFSG.Sporadic.SuzOddCore (suzM)
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (suzE81)

@[expose] noncomputable def EK (k : ℕ) : Equiv.Perm (Fin 1782) := φK (Multiplicative.ofAdd (vec k))

@[expose] noncomputable def qP (l : ℕ) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (unpack 1782 11 (qG l))

theorem prep_q {l : ℕ} (hl : l < 3) : PRep 1782 11 (qG l) (qP l) := prep_of_permB13637 (q_gen hl).2

theorem prep_one13637 : PRep 1782 11 (pidn 1782 11) 1 := prep_pidn (by norm_num) (by norm_num)

theorem strictB_q (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem vec_add5 (a b : ℕ) : vec (add5 a b) = vec a + vec b := by
  have hc : ∀ t, (dg3 a t + dg3 b t) % 3 < 3 := fun t => Nat.mod_lt _ (by norm_num)
  have e : add5 a b = (dg3 a 0 + dg3 b 0) % 3 + 3 * ((dg3 a 1 + dg3 b 1) % 3 + 3 *
      ((dg3 a 2 + dg3 b 2) % 3 + 3 * ((dg3 a 3 + dg3 b 3) % 3 + 3 * ((dg3 a 4 + dg3 b 4) % 3)))) :=
    rfl
  obtain ⟨h0, h1, h2, h3, h4⟩ := digit3_five (hc 0) (hc 1) (hc 2) (hc 3) (hc 4)
  funext t
  simp only [Pi.add_apply, vec]
  rw [e]
  fin_cases t <;> simp only [h0, h1, h2, h3, h4] <;> rw [ZMod.natCast_mod] <;> push_cast <;> rfl

theorem EK_add (a b : ℕ) : EK (add5 a b) = EK a * EK b := by
  unfold EK
  rw [vec_add5, ofAdd_add, map_mul]

theorem EK_zero : EK 0 = 1 := by
  have h : vec 0 = 0 := by
    funext i
    simp [vec, digit3]
  unfold EK
  rw [h, ofAdd_zero, map_one]

theorem EK_cube (k : ℕ) : EK k ^ 3 = 1 := by
  unfold EK
  rw [← map_pow]
  have h30 : ((3 : ℕ) : ZMod 3) = 0 := rfl
  have h : (Multiplicative.ofAdd (vec k)) ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, h30, zero_mul]
  rw [h, map_one]

theorem EK_dbl5 (k : ℕ) : EK (dbl5 k) = (EK k)⁻¹ := by
  have h3 := EK_cube k
  unfold EK at h3 ⊢
  rw [vec_dbl5, ofAdd_nsmul, map_pow]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)

theorem EK_mem (k : ℕ) : EK k ∈ DK := mem_DK k

theorem EK_inj {a b : ℕ} (ha : a < 243) (hb : b < 243) (h : EK a = EK b) : a = b := by
  have h1 := Multiplicative.ofAdd.injective (φK_injective h)
  rw [← idx_vec13637 ha, ← idx_vec13637 hb, h1]

theorem dbl5_lt (k : ℕ) : dbl5 k < 243 := by
  have hc : ∀ t, 2 * dg3 k t % 3 < 3 := fun t => Nat.mod_lt _ (by norm_num)
  have e : dbl5 k = 2 * dg3 k 0 % 3 + 3 * (2 * dg3 k 1 % 3 + 3 * (2 * dg3 k 2 % 3 +
      3 * (2 * dg3 k 3 % 3 + 3 * (2 * dg3 k 4 % 3)))) := rfl
  have := hc 0
  have := hc 1
  have := hc 2
  have := hc 3
  have := hc 4
  omega

theorem n_q {i : ℕ} (hi : i < 2) : inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP (qG (i + 1)) = true ∧
    ∀ l < 5, pcomp 1782 11 (mask 11) (qG (i + 1)) (nthN F.D l) =
      ePg 1782 11 F.D (nthN (nthL F.M i) l) (qG (i + 1)) := by
  have h0 := n_ok
  unfold nOK at h0
  have h := allN_iff.1 h0 i hi
  unfold withReb at h
  have hr := (nb_reb hi).1
  rcases e : rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => nthN (nthL F.nb i) l) 6 with
    ⟨g, gi, ok⟩
  rw [e] at h hr
  change strictB g (fun g => bAnd(ok, bAnd(inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP g,
    allN 5 fun l => Nat.beq (pcomp 1782 11 (mask 11) g (nthN F.D l))
      (ePg 1782 11 F.D (nthN (nthL F.M i) l) g)))) = true at h
  rw [Orb.strictB_eq, bAnd_eqS, bAnd_eqS, Bool.and_eq_true, Bool.and_eq_true] at h
  change g = qG (i + 1) at hr
  subst hr
  exact ⟨h.2.1, fun l hl => Nat.eq_of_beq_eq_true (allN_iff.1 h.2.2 l hl)⟩

theorem q_conj {i : ℕ} (hi : i < 2) (k : ℕ) :
    qP (i + 1) * EK k = EK (act5 (nthL F.M i) k) * qP (i + 1) := by
  obtain ⟨-, hql⟩ := n_q hi
  have hQ0 := prep_q (l := i + 1) (by omega)
  have hQ : ∀ l : Fin 5, qP (i + 1) * dPerm l =
      φK (Multiplicative.ofAdd (vec (nthN (nthL F.M i) l))) * qP (i + 1) := by
    intro l
    have h1 := prep_pcomp n32_13637 hQ0 (prep_d l.2)
    rw [hql l l.2] at h1
    exact prep_eq13637 h1 (prep_ePg hQ0 _)
  exact conj_φK hQ k

theorem qP_mem {i : ℕ} (hi : i < 2) :
    qP (i + 1) ∈ suzM :=
  (mem_of_inPK (n_q hi).1).2

theorem qrel_parts : qG 0 = ePg 1782 11 F.D 163 (pidn 1782 11) ∧
    pcomp 1782 11 (mask 11) (qG 1) (pcomp 1782 11 (mask 11) (qG 1) (qG 1)) =
      ePg 1782 11 F.D 42 (pidn 1782 11) ∧
    pcomp 1782 11 (mask 11) (qG 2) (pcomp 1782 11 (mask 11) (qG 2) (qG 2)) = pidn 1782 11 ∧
    pcomp 1782 11 (mask 11) (qG 2) (qG 1) =
      ePg 1782 11 F.D 51 (pcomp 1782 11 (mask 11) (qG 1) (qG 2)) := by
  have h := qrel_ok
  unfold CFSG.KS.QMdlK.relOK at h
  rw [bAnd_eqS, bAnd_eqS, bAnd_eqS, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem q0_eq : qP 0 = EK 163 := by
  have h1 := prep_q (l := 0) (by norm_num)
  rw [qrel_parts.1] at h1
  have h2 := prep_eq13637 h1 (prep_ePg prep_one13637 163)
  rw [h2, mul_one]
  rfl

theorem q1_cube : qP 1 ^ 3 = EK (nthN QM.qr 1) := by
  have hq := prep_q (l := 1) (by norm_num)
  have h1 := prep_pcomp n32_13637 hq (prep_pcomp n32_13637 hq hq)
  rw [qrel_parts.2.1] at h1
  have h2 := prep_eq13637 h1 (prep_ePg prep_one13637 42)
  rw [pow_three, h2, mul_one]
  rfl

theorem q2_cube : qP 2 ^ 3 = 1 := by
  have hq := prep_q (l := 2) (by norm_num)
  have h1 := prep_pcomp n32_13637 hq (prep_pcomp n32_13637 hq hq)
  rw [qrel_parts.2.2.1] at h1
  rw [pow_three]
  exact prep_eq13637 h1 prep_one13637

theorem q21 : qP 2 * qP 1 = EK (nthN QM.qr 2) * qP 1 * qP 2 := by
  have h1 := prep_q (l := 1) (by norm_num)
  have h2 := prep_q (l := 2) (by norm_num)
  have h3 := prep_pcomp n32_13637 h2 h1
  rw [qrel_parts.2.2.2] at h3
  rw [prep_eq13637 h3 (prep_ePg (prep_pcomp n32_13637 h1 h2) 51), mul_assoc]
  rfl

theorem qHyp : MHyp EK (qP 1) (qP 2) (nthL F.M 0) (nthL F.M 1) (nthN QM.qr 1) (nthN QM.qr 2) where
  e0 := EK_zero
  add := EK_add
  c1 := q_conj (i := 0) (by norm_num)
  c2 := q_conj (i := 1) (by norm_num)
  p1 := q1_cube
  p2 := q2_cube
  rr := q21

@[expose] noncomputable def mdlQ (c : ℕ) : Equiv.Perm (Fin 1782) := mdl EK (qP 1) (qP 2) c

theorem mdlQ_enc {v i j : ℕ} (hv : v < 243) (hi : i < 3) :
    mdlQ (v + 243 * (i + 3 * j)) = EK v * qP 1 ^ i * qP 2 ^ j := mdl_enc hv hi

theorem mdlQ_D {v : ℕ} (hv : v < 243) : mdlQ v = EK v := by
  have h := mdlQ_enc (v := v) (i := 0) (j := 0) hv (by norm_num)
  simpa using h

theorem mdlQ_mul {a b : ℕ} (ha : a < 2187) (hb : b < 2187) :
    mdlQ a * mdlQ b = mdlQ (mulC (nthL F.M 0) (nthL F.M 1) (nthN QM.qr 1) (nthN QM.qr 2) a b) ∧
      mulC (nthL F.M 0) (nthL F.M 1) (nthN QM.qr 1) (nthN QM.qr 2) a b < 2187 :=
  mdl_mulC qHyp ha hb

@[expose] noncomputable def SQm : Submonoid (Equiv.Perm (Fin 1782)) where
  carrier := {x | ∃ c < 2187, mdlQ c = x}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    obtain ⟨e, l⟩ := mdlQ_mul ha hb
    exact ⟨_, l, e.symm⟩
  one_mem' := ⟨0, by norm_num, by rw [mdlQ_D (by norm_num), EK_zero]⟩

theorem SQm_inv {x : Equiv.Perm (Fin 1782)} (hx : x ∈ SQm) : x⁻¹ ∈ SQm := by
  have hpos := (isOfFinOrder_of_finite x).orderOf_pos
  have e : x⁻¹ = x ^ (orderOf x - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [e]
  exact SQm.pow_mem hx _

@[expose] noncomputable def SQ : Subgroup (Equiv.Perm (Fin 1782)) :=
  { SQm with inv_mem' := SQm_inv }

theorem mem_SQ {x : Equiv.Perm (Fin 1782)} : x ∈ SQ ↔ ∃ c < 2187, mdlQ c = x := Iff.rfl

theorem qP_eq_mdl : qP 0 = mdlQ 163 ∧ qP 1 = mdlQ 243 ∧ qP 2 = mdlQ 729 := by
  have h1 := mdlQ_enc (v := 0) (i := 1) (j := 0) (by norm_num) (by norm_num)
  have h2 := mdlQ_enc (v := 0) (i := 0) (j := 1) (by norm_num) (by norm_num)
  norm_num at h1 h2
  rw [EK_zero, one_mul] at h1 h2
  exact ⟨by rw [q0_eq, mdlQ_D (by norm_num)], h1.symm, h2.symm⟩

theorem gen_eq {k : ℕ} (hk : k < 3) : permOfArr 1782 (qGensS ())[k]! = qP k := by
  unfold qP
  rw [(q_gen hk).1]

theorem qP_memQ {l : ℕ} (hl : l < 3) : qP l ∈ Qg :=
  Subgroup.subset_closure ⟨l, by rw [q_size]; exact hl, gen_eq hl⟩

theorem posWordK_mem : ∀ (wd : List ℕ), (∀ l ∈ wd, l < 3) → ∀ (A : ℕ) (X : Equiv.Perm (Fin 1782)),
    PRep 1782 11 A X → X ∈ Qg → ∃ Y ∈ Qg, PRep 1782 11 (List.rec (motive := fun _ => ℕ → ℕ)
      (fun acc => acc) (fun l _ ih acc => strictN (pcomp 1782 11 (mask 11) acc (qG l)) ih) wd A) Y
  | [], _, _, X, hA, hX => ⟨X, hX, hA⟩
  | l :: wd, hl, A, X, hA, hX => by
    have hl0 : l < 3 := hl l List.mem_cons_self
    have e : List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => strictN (pcomp 1782 11 (mask 11) acc (qG l)) ih) (l :: wd) A =
      List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => strictN (pcomp 1782 11 (mask 11) acc (qG l)) ih) wd
          (pcomp 1782 11 (mask 11) A (qG l)) := strictN_q _ _
    rw [e]
    exact posWordK_mem wd (fun k hk => hl k (List.mem_cons_of_mem l hk)) _ _
      (prep_pcomp n32_13637 hA (prep_q hl0)) (Qg.mul_mem hX (qP_memQ hl0))

theorem dPerm_memQ (i : Fin 5) : dPerm i ∈ Qg := by
  have hi' : i.val < (suzE81.dW[0]!).size := by rw [bind_letters.2.2.2]; exact i.2
  have e := map_nthN13637 bind_d hi'
  obtain ⟨Y, hY, hp⟩ := posWordK_mem _ (letters13637 bind_letters.2.1 i hi') (pidn 1782 11) 1
    prep_one13637 Qg.one_mem
  have hp' : PRep 1782 11 (nthN F.D i) Y := by
    rw [← e]
    exact hp
  rw [prep_eq13637 (prep_d i.2) hp']
  exact hY

theorem DKQ_le : DK ≤ Qg := by
  rintro _ ⟨a, rfl⟩
  change Co3T.vecProd dPerm a.toAdd ∈ Qg
  rw [vecProd_eq]
  have h := dPerm_memQ
  exact Qg.mul_mem (Qg.pow_mem (h 0) _) (Qg.mul_mem (Qg.pow_mem (h 1) _)
    (Qg.mul_mem (Qg.pow_mem (h 2) _) (Qg.mul_mem (Qg.pow_mem (h 3) _) (Qg.pow_mem (h 4) _))))

theorem Qg_eq_SQ : Qg = SQ := by
  apply le_antisymm
  · rw [Qg, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [q_size] at hk
    have hk3 : k < 3 := hk
    change permOfArr 1782 (qGensS ())[k]! ∈ SQ
    rw [gen_eq hk3]
    obtain ⟨h0, h1, h2⟩ := qP_eq_mdl
    interval_cases k
    · exact ⟨163, by norm_num, h0.symm⟩
    · exact ⟨243, by norm_num, h1.symm⟩
    · exact ⟨729, by norm_num, h2.symm⟩
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨v, i, j, hv, hi, hj, rfl⟩ := dec hc
    rw [mdlQ_enc hv hi]
    exact Qg.mul_mem (Qg.mul_mem (DKQ_le (EK_mem v)) (Qg.pow_mem (qP_memQ (by norm_num)) _))
      (Qg.pow_mem (qP_memQ (by norm_num)) _)

theorem pw3_lt (M : List ℕ) {i k : ℕ} (hi : i < 3) (hk : k < 243) : pw3 M i k < 243 := by
  interval_cases i
  · exact hk
  · exact act5_lt M k
  · exact act5_lt M _

theorem nact_lt {i j k : ℕ} (hi : i < 3) (hj : j < 3) (hk : k < 243) :
    nact (nthL F.M 0) (nthL F.M 1) i j k < 243 :=
  pw3_lt _ hi (pw3_lt _ hj hk)

theorem s_act {v v' i j i' j' : ℕ} (hi : i < 3) (hj : j < 3) (hi' : i' < 3) (hj' : j' < 3)
    (h : EK v * qP 1 ^ i * qP 2 ^ j = EK v' * qP 1 ^ i' * qP 2 ^ j') (k : ℕ) :
    EK (nact (nthL F.M 0) (nthL F.M 1) i j k) = EK (nact (nthL F.M 0) (nthL F.M 1) i' j' k) := by
  set s := qP 1 ^ i * qP 2 ^ j with hs
  set s' := qP 1 ^ i' * qP 2 ^ j' with hs'
  set n := nact (nthL F.M 0) (nthL F.M 1) i j k
  set n' := nact (nthL F.M 0) (nthL F.M 1) i' j' k
  have c1 : s * EK k = EK n * s := s_conj qHyp hi hj k
  have c2 : s' * EK k = EK n' * s' := s_conj qHyp hi' hj' k
  set d := (EK v')⁻¹ * EK v with hd
  have h' : EK v' * s' = EK v * s := by
    rw [hs, hs', ← mul_assoc, ← mul_assoc]
    exact h.symm
  have hdd : s' = d * s := by
    rw [hd, mul_assoc, ← h', ← mul_assoc, inv_mul_cancel, one_mul]
  have hdm : d ∈ DK := DK.mul_mem (DK.inv_mem (EK_mem v')) (EK_mem v)
  have hcomm : d * EK n = EK n * d := DK_comm _ hdm _ (EK_mem n)
  have e : EK n' * s' = EK n * s' := by
    rw [← c2, hdd, mul_assoc, c1, ← mul_assoc, hcomm, mul_assoc]
  exact (mul_right_cancel e).symm

theorem cdiv3 {i j : ℕ} (hi : i < 3) : Nat.div (i + 3 * j) 3 = j := by
  have h : (i + 3 * j) / 3 = j := by omega
  exact h

theorem dist_ne {u u' : ℕ} (hu : u < 9) (hu' : u' < 9) (hne : u ≠ u') : ∃ t < 5,
    nact (nthL F.M 0) (nthL F.M 1) (Nat.mod u 3) (Nat.div u 3) (Nat.pow 3 t) ≠
      nact (nthL F.M 0) (nthL F.M 1) (Nat.mod u' 3) (Nat.div u' 3) (Nat.pow 3 t) := by
  have h0 := qdist_ok
  unfold distOK at h0
  have h1 := allN_iff.1 (allN_iff.1 h0 u hu) u' hu'
  have hb : Nat.beq u u' = false := by
    cases hb : Nat.beq u u'
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne
  simp only [hb] at h1
  by_contra hc
  push Not at hc
  have hall : allN 5 (fun t => Nat.beq (nact (nthL F.M 0) (nthL F.M 1) (Nat.mod u 3) (Nat.div u 3)
      (Nat.pow 3 t)) (nact (nthL F.M 0) (nthL F.M 1) (Nat.mod u' 3) (Nat.div u' 3)
        (Nat.pow 3 t))) = true :=
    allN_iff.2 fun t ht => by rw [hc t ht]; exact Nat.beq_refl _
  simp only [hall] at h1
  exact absurd h1 (by decide)

theorem mdlQ_inj {a b : ℕ} (ha : a < 2187) (hb : b < 2187) (h : mdlQ a = mdlQ b) : a = b := by
  obtain ⟨v, i, j, hv, hi, hj, rfl⟩ := dec ha
  obtain ⟨v', i', j', hv', hi', hj', rfl⟩ := dec hb
  rw [mdlQ_enc hv hi, mdlQ_enc hv' hi'] at h
  have hu : i = i' ∧ j = j' := by
    by_contra hne
    obtain ⟨t, ht, hne'⟩ := dist_ne (u := i + 3 * j) (u' := i' + 3 * j') (by omega) (by omega)
      (fun e => hne ⟨by omega, by omega⟩)
    rw [cimod hi, cimod hi', cdiv3 hi, cdiv3 hi'] at hne'
    have hpt : Nat.pow 3 t < 243 := by
      have : 3 ^ t ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e3 : Nat.pow 3 t = 3 ^ t := rfl
      rw [e3]
      omega
    exact hne' (EK_inj (nact_lt hi hj hpt) (nact_lt hi' hj' hpt) (s_act hi hj hi' hj' h _))
  obtain ⟨rfl, rfl⟩ := hu
  rw [mul_assoc, mul_assoc] at h
  rw [EK_inj hv hv' (mul_right_cancel h)]

theorem card_QgK : Nat.card Qg = 2187 := by
  rw [Qg_eq_SQ]
  have hset : (SQ : Set (Equiv.Perm (Fin 1782))) = ↑((Finset.range 2187).image mdlQ) := by
    ext x
    simp only [SetLike.mem_coe, mem_SQ, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio]
  have hinj : Set.InjOn mdlQ ↑(Finset.range 2187) := fun a ha b hb h =>
    mdlQ_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
  have e : Nat.card SQ = Nat.card ↥(SQ : Set (Equiv.Perm (Fin 1782))) := rfl
  rw [e, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj,
    Finset.card_range]

theorem QgK_le : Qg ≤ suzM := by
  rw [Qg_eq_SQ]
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨v, i, j, hv, hi, hj, rfl⟩ := dec hc
  rw [mdlQ_enc hv hi]
  exact suzM.mul_mem (suzM.mul_mem (DK_le (EK_mem v)) (suzM.pow_mem (qP_mem (i := 0)
    (by norm_num)) _)) (suzM.pow_mem (qP_mem (i := 1) (by norm_num)) _)

theorem allIx_spec {f : ℕ → ℕ → Bool} : ∀ (l : List ℕ) (s : ℕ), allIx f l s = true →
    ∀ i < l.length, f (s + i) (nthN l i) = true
  | [], _, _, i, hi => absurd hi (by simp)
  | e :: l, s, h, i, hi => by
    have h' : bAnd(f s e, strictB (Nat.succ s) (allIx f l)) = true := h
    rw [bAnd_eqS, Bool.and_eq_true, strictB_q] at h'
    cases i with
    | zero => exact h'.1
    | succ i =>
      have h2 := allIx_spec l (s + 1) h'.2 i (by simp at hi; omega)
      have e : s + (i + 1) = s + 1 + i := by omega
      rw [e]
      exact h2

theorem fus_parts : (∀ j < 12, nthN QM.lc j < 2187) ∧ ∀ c < 2187,
    fusAt (nthL F.M 0) (nthL F.M 1) (nthN QM.qr 1) (nthN QM.qr 2) QM.lc c (nthN QM.fb c) = true := by
  have h := qfus_ok
  unfold fusOK at h
  rw [bAnd_eqS, bAnd_eqS, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hl : QM.fb.length = 2187 := Nat.eq_of_beq_eq_true h2
  refine ⟨fun j hj => ?_, fun c hc => ?_⟩
  · have h4 := allN_iff.1 h1 j hj
    rw [Nat.blt_eq] at h4
    exact h4
  · have h4 := allIx_spec QM.fb 0 h3 c (by rw [hl]; exact hc)
    rwa [Nat.zero_add] at h4

theorem fusAt_spec {M1 M2 : List ℕ} {r1 r2 c e : ℕ} {lc : List ℕ}
    (h : fusAt M1 M2 r1 r2 lc c e = true) (hc : 243 ≤ c) (h3 : cubeC M1 M2 r1 r2 c = 0) :
    Nat.div e 243 < 24 ∧ mulC M1 M2 r1 r2 (mulC M1 M2 r1 r2 (Nat.mod e 243) c)
      (dbl5 (Nat.mod e 243)) = repC M1 M2 r1 r2 lc (Nat.div e 243) := by
  unfold fusAt at h
  have hb : Nat.blt c 243 = false := by
    cases hb : Nat.blt c 243
    · rfl
    · rw [Nat.blt_eq] at hb
      omega
  have hb2 : Nat.beq (cubeC M1 M2 r1 r2 c) 0 = true := by rw [h3]; rfl
  simp only [hb, hb2] at h
  rw [bAnd_eqS, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem repC_lt {M1 M2 : List ℕ} {r1 r2 r : ℕ} {lc : List ℕ} (hr : r < 12) :
    repC M1 M2 r1 r2 lc r = nthN lc r := by
  have hb : Nat.blt r 12 = true := by rw [Nat.blt_eq]; exact hr
  unfold repC
  simp only [hb]

theorem repC_ge {M1 M2 : List ℕ} {r1 r2 r : ℕ} {lc : List ℕ} (hr : ¬ r < 12) :
    repC M1 M2 r1 r2 lc r = mulC M1 M2 r1 r2 (nthN lc (Nat.sub r 12)) (nthN lc (Nat.sub r 12)) := by
  have hb : Nat.blt r 12 = false := by
    cases hb : Nat.blt r 12
    · rfl
    · rw [Nat.blt_eq] at hb
      exact absurd hb hr
  unfold repC
  simp only [hb]

theorem prep_mdlP {c : ℕ} (hc : c < 2187) :
    PRep 1782 11 (mdlP 1782 11 F.D Q1 Q2 c) (mdlQ c) := by
  obtain ⟨v, i, j, hv, hi, hj, rfl⟩ := dec hc
  unfold mdlP
  rw [cmod hv, cdiv hv, cimod hi, cdiv729 hv hi, mdlQ_enc hv hi]
  have hq1 : PRep 1782 11 Q1 (qP 1) := prep_q (l := 1) (by norm_num)
  have hq2 : PRep 1782 11 Q2 (qP 2) := prep_q (l := 2) (by norm_num)
  have h2 := prep_mulD hq2 prep_one13637 hj
  have h1 := prep_mulD hq1 h2 hi
  have h0 := prep_ePg h1 v
  rw [mul_one] at h0
  have e : EK v * qP 1 ^ i * qP 2 ^ j =
      φK (Multiplicative.ofAdd (vec v)) * (qP 1 ^ i * qP 2 ^ j) := by
    rw [mul_assoc]
    rfl
  rw [e]
  exact h0

theorem tr_parts {j : ℕ} (hj : j < 12) :
    inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP (nthN QM.H j) = true ∧
    (nthN QM.z j = 0 → pcomp 1782 11 (mask 11) (nthN QM.H j) (mdlP 1782 11 F.D Q1 Q2 (nthN QM.lc j)) =
      pcomp 1782 11 (mask 11) CD.Y (nthN QM.H j)) ∧
    (nthN QM.z j ≠ 0 → pcomp 1782 11 (mask 11) (nthN QM.H j) (mdlP 1782 11 F.D Q1 Q2 (nthN QM.lc j)) =
      ePg 1782 11 F.D (Nat.sub (nthN QM.z j) 243) (nthN QM.H j)) := by
  have h0 := qtr_ok
  unfold trOK at h0
  have h := allN_iff.1 h0 j hj
  rw [strictB_q, bAnd_eqS, Bool.and_eq_true, strictB_q] at h
  refine ⟨h.1, fun hz => ?_, fun hz => ?_⟩
  · have hb : Nat.beq (nthN QM.z j) 0 = true := by rw [hz]; rfl
    have h2 := h.2
    simp only [hb] at h2
    exact Nat.eq_of_beq_eq_true h2
  · have hb : Nat.beq (nthN QM.z j) 0 = false := by
      cases hb : Nat.beq (nthN QM.z j) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hz
    have h2 := h.2
    simp only [hb] at h2
    exact Nat.eq_of_beq_eq_true h2

theorem trans_j {j : ℕ}
    (hj : j < 12) : ∃ H ∈ suzM, H * mdlQ (nthN QM.lc j) * H⁻¹ ∈ DK ∨
      H * mdlQ (nthN QM.lc j) * H⁻¹ = yP := by
  obtain ⟨hin, hy, hd⟩ := tr_parts hj
  obtain ⟨hp, hm⟩ := mem_of_inPK hin
  have hH := prep_of_permB13637 hp
  have hHR := prep_pcomp n32_13637 hH (prep_mdlP (fus_parts.1 j hj))
  refine ⟨_, hm, ?_⟩
  by_cases hz : nthN QM.z j = 0
  · right
    rw [hy hz] at hHR
    rw [prep_eq13637 hHR (prep_pcomp n32_13637 prep_Y hH), mul_inv_cancel_right]
  · left
    rw [hd hz] at hHR
    rw [prep_eq13637 hHR (prep_ePg hH _), mul_inv_cancel_right]
    exact mem_DK _

theorem fusion_q {t : Equiv.Perm (Fin 1782)} (ht : t ∈ Qg) (h3 : t ^ 3 = 1) : t ∈ DK ∨
    ∃ b < 243, ∃ j < 12, EK b * t * (EK b)⁻¹ = mdlQ (nthN QM.lc j) ∨
      EK b * t * (EK b)⁻¹ = mdlQ (nthN QM.lc j) ^ 2 := by
  rw [Qg_eq_SQ] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  by_cases hc0 : c < 243
  · left
    rw [mdlQ_D hc0]
    exact EK_mem c
  right
  obtain ⟨hcube, hcl⟩ := mdl_cubeC qHyp hc
  have hc3 : mdlQ (cubeC (nthL F.M 0) (nthL F.M 1) (nthN QM.qr 1) (nthN QM.qr 2) c) = mdlQ 0 := by
    rw [mdlQ_D (v := 0) (by norm_num), EK_zero]
    exact hcube.symm.trans h3
  have h0 := mdlQ_inj hcl (by norm_num) hc3
  obtain ⟨hr, he⟩ := fusAt_spec (fus_parts.2 c hc) (by omega) h0
  have hb : Nat.mod (nthN QM.fb c) 243 < 243 := Nat.mod_lt _ (by norm_num)
  obtain ⟨m1, l1⟩ := mdlQ_mul (by omega) hc (a := Nat.mod (nthN QM.fb c) 243)
  obtain ⟨m2, -⟩ := mdlQ_mul l1 ((dbl5_lt (Nat.mod (nthN QM.fb c) 243)).trans (by norm_num))
  have hconj : EK (Nat.mod (nthN QM.fb c) 243) * mdlQ c * (EK (Nat.mod (nthN QM.fb c) 243))⁻¹ =
      mdlQ (repC (nthL F.M 0) (nthL F.M 1) (nthN QM.qr 1) (nthN QM.qr 2) QM.lc
        (Nat.div (nthN QM.fb c) 243)) := by
    rw [← he, ← m2, ← m1, mdlQ_D hb, mdlQ_D (dbl5_lt _), EK_dbl5]
  refine ⟨_, hb, ?_⟩
  by_cases hr12 : Nat.div (nthN QM.fb c) 243 < 12
  · exact ⟨_, hr12, Or.inl (hconj.trans (by rw [repC_lt hr12]))⟩
  · have hj : Nat.sub (Nat.div (nthN QM.fb c) 243) 12 < 12 := by
      have e : Nat.sub (Nat.div (nthN QM.fb c) 243) 12 = nthN QM.fb c / 243 - 12 := rfl
      have e2 : Nat.div (nthN QM.fb c) 243 = nthN QM.fb c / 243 := rfl
      rw [e]
      rw [e2] at hr hr12
      omega
    refine ⟨_, hj, Or.inr (hconj.trans ?_)⟩
    rw [repC_ge hr12, ← (mdlQ_mul (fus_parts.1 _ hj) (fus_parts.1 _ hj)).1, pow_two]

theorem fusion_suzK
    {x : Equiv.Perm (Fin 1782)} (hx : x ∈ suzM) (hxo : orderOf x = 3) :
    ∃ h ∈ suzM, h * x * h⁻¹ ∈ DK ∨ h * x * h⁻¹ = yP ∨ h * x * h⁻¹ = yP ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgP, hgQ⟩ := Co3T.exists_conj_mem_of_full QgK_le
    (by rw [card_QgK, factorization_card_suzM_three]; norm_num) hx hxo
  set t := g⁻¹ * x * g with htdef
  have hto : orderOf t = 3 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 1782) ≃* Equiv.Perm (Fin 1782)).orderOf_eq x
    simpa [MulAut.conj_apply, htdef, hxo] using this
  have ht3 : t ^ 3 = 1 := hto ▸ pow_orderOf_eq_one t
  rcases fusion_q hgQ ht3 with hD | ⟨b, -, j, hj, hL⟩
  · refine ⟨g⁻¹, suzM.inv_mem hgP, Or.inl ?_⟩
    rw [inv_inv]
    exact hD
  obtain ⟨H, hH, hcase⟩ := trans_j hj
  refine ⟨H * EK b * g⁻¹, suzM.mul_mem (suzM.mul_mem hH (DK_le (EK_mem b))) (suzM.inv_mem hgP), ?_⟩
  have hkey : H * EK b * g⁻¹ * x * (H * EK b * g⁻¹)⁻¹ = H * (EK b * t * (EK b)⁻¹) * H⁻¹ := by
    rw [htdef]
    group
  rw [hkey]
  rcases hL with hL | hL
  · rw [hL]
    rcases hcase with hD | hy
    · exact Or.inl hD
    · exact Or.inr (Or.inl hy)
  · rw [hL, ← conj_pow]
    rcases hcase with hD | hy
    · exact Or.inl (DK.pow_mem hD 2)
    · rw [hy]
      exact Or.inr (Or.inr rfl)

end CFSG.KD.SuzThree13637

end
