module

public import Certificates.Kernel.Sporadic.Fi22.T2064
public import Certificates.Kernel.Sporadic.Fi22.R2064
public import CFSG.Certificates.Kernel.Spor.MulTreeSound
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrder
public import CFSG.Sporadic.FischerOddCore.ClosureSpec
public import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs
public import CFSG.Monster.B.Fischer.Fi22Order
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Sporadic.Fi22.C3151

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CtiA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.MulTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor
open CFSG.Sporadic.FischerOddCore.Native
open CertificateChecks.KernelSpor.Fi22CtiX

theorem bp_lt {t : Nat} (ht : t < 6) : bp t < 3510 := by
  interval_cases t <;> decide

theorem bp_mem {t : Nat} (ht : t < 6) : bp t ∈ ([0, 1, 2, 3, 6, 4] : List Nat) := by
  interval_cases t <;> decide

theorem sepP
    {X Y : Equiv.Perm (Fin 3510)} (hX : X ∈ fi22P) (hY : Y ∈ fi22P)
    (h : ∀ t (ht : t < 6), (X ⟨bp t, bp_lt ht⟩ : Nat) = Y ⟨bp t, bp_lt ht⟩) : X = Y := by
  have hG : Y⁻¹ * X ∈ fi22P := fi22P.mul_mem (fi22P.inv_mem hY) hX
  have h1 : Y⁻¹ * X = 1 := by
    refine fi22Chain.eq_one_of_fixes_base fi22Chain_valid.1 hG fun i => ?_
    have hv : ((fi22Chain.base.get i : Fin 3510) : ℕ) = fi22BaseArr[(i : ℕ)]! :=
      fi22ChainArrays.base_val i
    have hi : (i : ℕ) < 6 := i.2
    have hb : fi22BaseArr[(i : ℕ)]! = bp i := by
      obtain ⟨i, hi'⟩ := i
      change i < 6 at hi
      interval_cases i <;> rfl
    have e : fi22Chain.base.get i = ⟨bp i, bp_lt hi⟩ := Fin.ext (hv.trans hb)
    rw [e, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (h i hi)
  rw [mul_eq_one_iff_eq_inv] at h1
  exact (inv_injective h1).symm

theorem cn_lt {q : Nat} (h : cn q = true) : ∀ x < 3510, pg 12 (mask 12) q x < 3510 := by
  have h' : bAnd(szOK 3510 12, bAnd(Nat.beq (Nat.shiftRight q (3510 * 12)) (nat_lit 0),
      allN 3510 (fun i => Nat.blt (pg 12 (mask 12) q i) 3510))) = true := h
  obtain ⟨-, h2⟩ := (bAnd_iff (szOK 3510 12) (bAnd(Nat.beq (Nat.shiftRight q (3510 * 12))
    (nat_lit 0), allN 3510 (fun i => Nat.blt (pg 12 (mask 12) q i) 3510)))).1 h'
  have h3 := ((bAnd_iff (Nat.beq (Nat.shiftRight q (3510 * 12)) (nat_lit 0))
    (allN 3510 (fun i => Nat.blt (pg 12 (mask 12) q i) 3510))).1 h2).2
  intro x hx
  exact Nat.blt_eq ▸ allN_spec h3 x hx

theorem eqA_of_get {t u : Array Nat} (h : ∀ z < 3510, t[z]! = u[z]!) : eqA 3510 t u = true := by
  rw [eqA, allLt_iff]
  intro z hz
  rw [beq_iff_eq, h z hz]

theorem strictIncr_of_pairwise : ∀ {l : List Nat}, l.Pairwise (· < ·) → strictIncr l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [strictIncr, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, strictIncr_of_pairwise h.of_cons⟩

theorem keysOK_of_nodup {n : Nat} {b : List Nat} {E : Array (Array Nat)}
    (h : (E.toList.map (keyAt n b)).Nodup) : keysOK n b E = true := by
  unfold keysOK
  apply strictIncr_of_pairwise
  have hs := List.pairwise_mergeSort (le := fun a c => decide (a ≤ c))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (E.toList.map (keyAt n b))
  have hnd := (List.mergeSort_perm (E.toList.map (keyAt n b)) (fun a c => decide (a ≤ c))).nodup_iff.2 h
  refine (hs.and hnd).imp ?_
  intro a c ⟨hac, hne⟩
  simp only [decide_eq_true_eq] at hac
  omega

theorem not_allN {n : Nat} {f : Nat → Bool} (h : Bool.not (allN n f) = true) :
    ∃ i < n, f i ≠ true := by
  by_contra hc
  push Not at hc
  rw [allN_of_forall hc] at h
  exact absurd h (by decide)

noncomputable def gl (L : Nat) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (unpack 3510 12 (Fi22CentT.L L))

theorem rep_gl {L : Nat} (hL : L < 306) : Rep 3510 (unpack 3510 12 (Fi22CentT.L L)) (gl L) ∧
    Rep 3510 (unpack 3510 12 (Fi22E2065.CI L)) (gl L)⁻¹ ∧
    invCand 3510 (unpack 3510 12 (Fi22CentT.L L)) = unpack 3510 12 (Fi22E2065.CI L) := by
  have h := invEqK_sound (Fi22E2065.perm hL)
  exact ⟨(rep_permOfArr h.2).1, (rep_permOfArr h.2).2, h.1⟩

theorem cent_eq (htext : fi22Cent3510Text = Fi22E2065.textP) {L : Nat} (hL : L < 306) :
    fi22CentArr L = unpack 3510 12 (Fi22CentT.L L) := by
  rw [fi22CentArr, fi22CentBytes, htext, Fi22E2065.cent_eq hL]

theorem strong_mem_H1 {j : Nat} (hj : j < (fi22CentStrong 1).size) :
    permOfArr 3510 (fi22CentStrong 1)[j]! ∈ fi22H 1 := by
  have hV := fi22HChain_valid (c := 1) (by norm_num)
  have hj' : j < (fi22HChain 1).strongCount := hj
  have h := RawSchreierDatum.strong_get_mem_originalSubgroup (fi22HChain 1) hV ⟨j, hj'⟩
  have e : (fi22HChain 1).strong.get ⟨j, hj'⟩ = permOfArr 3510 (fi22CentStrong 1)[j]! :=
    RawSchreierDatum.ofArrays_strong_get (n := 3510) ⟨j, hj'⟩
  rwa [e] at h

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bOr_iff (a b : Bool) : bOr a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  ⟨allN_spec, allN_of_forall⟩

theorem unpack_get' {n w P x : Nat} (hx : x < n) : (unpack n w P)[x]! = pg w (mask w) P x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem unpack_size {n w P : Nat} : (unpack n w P).size = n := by
  simp [unpack]

theorem mask_eq (x : Nat) : mask x = 2 ^ x - 1 := by
  change (1 <<< x) - 1 = 2 ^ x - 1
  rw [Nat.one_shiftLeft]

theorem pg_row {w m P i t : Nat} (ht : t < m) :
    pg w (mask w) (pg (m * w) (mask (m * w)) P i) t = pg w (mask w) P (i * m + t) := by
  unfold pg
  rw [mask_eq, mask_eq]
  change ((P >>> (m * w * i) &&& (2 ^ (m * w) - 1)) >>> (w * t) &&& (2 ^ w - 1)) =
    (P >>> (w * (i * m + t)) &&& (2 ^ w - 1))
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < w
  · have h1 : w * t + j < m * w := by nlinarith
    have h2 : m * w * i + (w * t + j) = w * (i * m + t) + j := by ring
    simp [hj, h1, h2]
  · simp [hj]

theorem rowsOf_unpack {m k w N F : Nat} {PS : Nat → Nat} (hm : 0 < m) (hN : N = k * m)
    (h : ∀ j < k, PS j = pg (m * w) (mask (m * w)) F j) :
    rowsOf m (unpack N w F) = Array.ofFn (n := k) fun j => unpack m w (PS j.val) := by
  subst hN
  apply Array.ext
  · simp [rowsOf, unpack, Nat.mul_div_cancel k hm]
  · intro i h1 h2
    have hi : i < k := by simpa using h2
    have hle : i * m + m ≤ k * m := by
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hi)
      rwa [Nat.succ_mul] at h
    apply Array.ext
    · simp [rowsOf, unpack]
      omega
    · intro t t1 t2
      have ht : t < m := by simpa [unpack] using t2
      simp only [rowsOf, unpack, Array.getElem_ofFn, Array.getElem_extract]
      rw [h i hi, pg_row ht]

theorem inj_of_sorted {N : Nat} {f σ : Nat → Nat} (hσ : ∀ m < N, σ m < N)
    (hinc : ∀ m, m + 1 < N → f (σ m) < f (σ (m + 1))) :
    ∀ i < N, ∀ j < N, f i = f j → i = j := by
  have mono : ∀ a b, a < b → b < N → f (σ a) < f (σ b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact lt_trans (ih h (by omega)) (hinc b hb)
      · subst h
        exact hinc a hb
  have hinj : Set.InjOn σ (Finset.range N : Set Nat) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd (hab ▸ mono a b h hb) (lt_irrefl _)
    · exact absurd (hab ▸ mono b a h ha) (lt_irrefl _)
  have himg : (Finset.range N).image σ = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hσ a (Finset.mem_range.1 ha))
    · rw [Finset.card_image_of_injOn hinj]
  have hsurj : ∀ i < N, ∃ a < N, σ a = i := by
    intro i hi
    have : i ∈ (Finset.range N).image σ := by rw [himg]; exact Finset.mem_range.2 hi
    obtain ⟨a, ha, e⟩ := Finset.mem_image.1 this
    exact ⟨a, Finset.mem_range.1 ha, e⟩
  intro i hi j hj hij
  obtain ⟨a, ha, rfl⟩ := hsurj i hi
  obtain ⟨b, hb, rfl⟩ := hsurj j hj
  by_contra hne
  have hab : a ≠ b := fun h => hne (h ▸ rfl)
  rcases lt_or_gt_of_ne hab with h | h
  · exact absurd hij (ne_of_lt (mono a b h hb))
  · exact absurd hij (ne_of_gt (mono b a h ha))

theorem q_parts {j : Nat} (hj : j < 10) : cn (Q j) = true ∧ cn (Q (10 + j)) = true ∧
    permOK 3510 12 (mask 12) (3510 * 12) (Q j) (Q (10 + j)) = true := by
  have h := allN_spec qRows j hj
  unfold qRow at h
  obtain ⟨h1, h2, h3⟩ := by simpa only [bAnd_iff] using h
  exact ⟨h1, h2, h3⟩

theorem g_parts {k : Nat} (hk : k < 9) : cn (gL k) = true ∧ cn (gI k) = true := by
  have h := allN_spec gRows k hk
  unfold gRow at h
  obtain ⟨h1, h2⟩ := by simpa only [bAnd_iff] using h
  exact ⟨h1, h2⟩

theorem z_parts : cn (Q 20) = true ∧ Q 20 = pc (Q 6) (pc (Q 2) (pc (Q 16) (Q 12))) := by
  obtain ⟨h1, h2⟩ := by simpa only [bAnd_iff] using zEq
  exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩

theorem id_parts : idK 3510 12 (mask 12) = true ∧ cn (pidn 3510 12) = true := by
  obtain ⟨h1, h2⟩ := by simpa only [bAnd_iff] using idOK
  exact ⟨h1, h2⟩

theorem cnQ {j : Nat} (hj : j < 21) : cn (Q j) = true := by
  rcases Nat.lt_or_ge j 10 with h | h
  · exact (q_parts h).1
  · rcases Nat.lt_or_ge j 20 with h' | h'
    · have e : j = 10 + (j - 10) := by omega
      rw [e]
      exact (q_parts (j := j - 10) (by omega)).2.1
    · have e : j = 20 := by omega
      rw [e]
      exact z_parts.1

theorem pw_succ (p k : Nat) : pw p (k + 1) = pc p (pw p k) := by
  change strictN (pw p k) (fun q => pcomp 3510 12 (mask 12) p q) = pc p (pw p k)
  exact strictN_eq' _ _

theorem pw_cn {p : Nat} (hp : cn p = true) : ∀ k, cn (pw p k) = true
  | 0 => by
    have h := id_parts.2
    exact h
  | k + 1 => by
    rw [pw_succ]
    exact canonK_pcomp hp (pw_cn hp k)

theorem unpack_id : unpack 3510 12 (pidn 3510 12) = idA 3510 := idK_sound id_parts.1

theorem powA_unpack {p : Nat} (hp : cn p = true) :
    ∀ k, CFSG.Sporadic.FischerOddCore.Native.powA 3510 (unpack 3510 12 p) k =
      unpack 3510 12 (pw p k)
  | 0 => by
    rw [CFSG.Sporadic.FischerOddCore.Native.powA]
    exact unpack_id.symm
  | k + 1 => by
    rw [CFSG.Sporadic.FischerOddCore.Native.powA, powA_unpack hp k,
      compA_unpack hp (pw_cn hp k), pw_succ]
    rfl

section Text

variable (htext : fi22Cent3510Text = Fi22E2065.textP)
include htext

theorem ctiG_eq {k : Nat} (hk : k < 9) : ctiG k = unpack 3510 12 (gL k) :=
  cent_eq htext (L := 19 + k) (by omega)

theorem ctiGi_eq {k : Nat} (hk : k < 9) : ctiGi k = unpack 3510 12 (gI k) := by
  rw [ctiGi, ctiG_eq htext hk]
  exact (rep_gl (L := 19 + k) (by omega)).2.2

theorem ctiQ3_eq : ctiQ3 = unpack 3510 12 (Q 2) := by
  have c2 := (g_parts (k := 2) (by norm_num)).1
  have c6 := (g_parts (k := 6) (by norm_num)).1
  rw [ctiQ3, ctiG_eq htext (by norm_num), ctiG_eq htext (by norm_num), compA_unpack c2 c6,
    powA_unpack (canonK_pcomp c2 c6) 6]
  exact (congrArg (unpack 3510 12) (Nat.eq_of_beq_eq_true qEq2)).symm

theorem pow_case {a b e j : Nat} (ha : a < 9) (hb : b < 9)
    (hq : Nat.beq (Q j) (pw (pc (gL a) (gL b)) e) = true) :
    CFSG.Sporadic.FischerOddCore.Native.powA 3510 (compA 3510 (ctiG a) (ctiG b)) e =
      unpack 3510 12 (Q j) := by
  have ca := (g_parts ha).1
  have cb := (g_parts hb).1
  rw [ctiG_eq htext ha, ctiG_eq htext hb, compA_unpack ca cb, powA_unpack (canonK_pcomp ca cb) e]
  exact (congrArg (unpack 3510 12) (Nat.eq_of_beq_eq_true hq)).symm

theorem conj_case {a j : Nat} (ha : a < 9)
    (hq : Nat.beq (Q j) (pc (gL a) (pc (Q 2) (gI a))) = true) :
    conjArr 3510 (ctiG a) (ctiGi a) ctiQ3 = unpack 3510 12 (Q j) := by
  have ca := (g_parts ha).1
  have ci := (g_parts ha).2
  have c2 := cnQ (j := 2) (by norm_num)
  rw [conjArr, ctiG_eq htext ha, ctiGi_eq htext ha, ctiQ3_eq htext, compA_unpack c2 ci,
    compA_unpack ca (canonK_pcomp c2 ci)]
  exact (congrArg (unpack 3510 12) (Nat.eq_of_beq_eq_true hq)).symm

omit htext in
theorem ctiQArr_size : ctiQArr.size = 10 := Array.size_ofFn

theorem ctiQArr_get {j : Nat} (hj : j < 10) : ctiQArr[j]! = unpack 3510 12 (Q j) := by
  rw [ctiQArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  interval_cases j
  · change ctiG 0 = _
    rw [ctiG_eq htext (by norm_num)]
    exact (congrArg (unpack 3510 12) (Nat.eq_of_beq_eq_true qEq0)).symm
  · exact pow_case htext (by norm_num) (by norm_num) qEq1
  · exact ctiQ3_eq htext
  · exact pow_case htext (by norm_num) (by norm_num) qEq3
  · exact pow_case htext (by norm_num) (by norm_num) qEq4
  · exact pow_case htext (by norm_num) (by norm_num) qEq5
  · exact pow_case htext (by norm_num) (by norm_num) qEq6
  · exact conj_case htext (by norm_num) qEq7
  · exact conj_case htext (by norm_num) qEq8
  · exact conj_case htext (by norm_num) qEq9

theorem ctiQ_inv {j : Nat} (hj : j < 10) :
    invCand 3510 ctiQArr[j]! = unpack 3510 12 (Q (10 + j)) ∧
      isInvA 3510 ctiQArr[j]! (unpack 3510 12 (Q (10 + j))) = true := by
  rw [ctiQArr_get htext hj]
  exact invEqK_sound (q_parts hj).2.2

theorem ctiZ_eq : ctiZ = unpack 3510 12 (Q 20) := by
  have c6 := cnQ (j := 6) (by norm_num)
  have c2 := cnQ (j := 2) (by norm_num)
  have c16 := cnQ (j := 16) (by norm_num)
  have c12 := cnQ (j := 12) (by norm_num)
  rw [ctiZ, (ctiQ_inv htext (j := 6) (by norm_num)).1, (ctiQ_inv htext (j := 2) (by norm_num)).1,
    ctiQArr_get htext (j := 6) (by norm_num), ctiQArr_get htext (j := 2) (by norm_num)]
  change compA 3510 (unpack 3510 12 (Q 6)) (compA 3510 (unpack 3510 12 (Q 2))
    (compA 3510 (unpack 3510 12 (Q 16)) (unpack 3510 12 (Q 12)))) = _
  rw [compA_unpack c16 c12, compA_unpack c2 (canonK_pcomp c16 c12),
    compA_unpack c6 (canonK_pcomp c2 (canonK_pcomp c16 c12))]
  exact (congrArg (unpack 3510 12) z_parts.2).symm

end Text

noncomputable def QP (j : Nat) : Equiv.Perm (Fin 3510) := permOfArr 3510 (unpack 3510 12 (Q j))

theorem rep_Q {j : Nat} (hj : j < 10) : Rep 3510 (unpack 3510 12 (Q j)) (QP j) ∧
    Rep 3510 (unpack 3510 12 (Q (10 + j))) (QP j)⁻¹ := by
  have h := invEqK_sound (q_parts hj).2.2
  rw [h.1] at *
  exact ⟨(rep_permOfArr h.2).1, (rep_permOfArr h.2).2⟩

noncomputable def GP (k : Nat) : Equiv.Perm (Fin 3510) := gl (19 + k)

theorem rep_G {k : Nat} (hk : k < 9) : Rep 3510 (unpack 3510 12 (gL k)) (GP k) ∧
    Rep 3510 (unpack 3510 12 (gI k)) (GP k)⁻¹ :=
  ⟨(rep_gl (L := 19 + k) (by omega)).1, (rep_gl (L := 19 + k) (by omega)).2.1⟩

section Members

variable (htext : fi22Cent3510Text = Fi22E2065.textP)
include htext

theorem rep_G' {k : Nat} (hk : k < 9) : Rep 3510 (ctiG k) (GP k) ∧ Rep 3510 (ctiGi k) (GP k)⁻¹ := by
  rw [ctiG_eq htext hk, ctiGi_eq htext hk]
  exact rep_G hk

theorem GP_H {k : Nat} (hk : k < 9) : GP k ∈ fi22H 1 := by
  have hs : (fi22CentStrong 1).size = 16 := by rw [fi22CentStrong, Array.size_ofFn]; rfl
  have h := strong_mem_H1 (j := k) (by rw [hs]; omega)
  rw [fi22CentStrong_get (c := 1) (by norm_num) (by change k < 16; omega),
    cent_eq htext (by change 19 + k < 306; omega)] at h
  exact h

omit htext in
theorem H1_le_P :
    fi22H 1 ≤ fi22P := fun _ h => ((fi22H_le (c := 1) (by norm_num)) h).1

theorem GP_P
    {k : Nat} (hk : k < 9) : GP k ∈ fi22P := H1_le_P (GP_H htext hk)

theorem pow_rep {a b e : Nat} (ha : a < 9) (hb : b < 9) :
    ∃ X ∈ fi22H 1, Rep 3510
    (CFSG.Sporadic.FischerOddCore.Native.powA 3510 (compA 3510 (ctiG a) (ctiG b)) e) X :=
  ⟨(GP a * GP b) ^ e, Subgroup.pow_mem _ (Subgroup.mul_mem _ (GP_H htext ha) (GP_H htext hb)) e,
    rep_powA (rep_compA (rep_G' htext ha).1 (rep_G' htext hb).1) e⟩

theorem conj_rep {a : Nat} (ha : a < 9) :
    ∃ X ∈ fi22H 1, Rep 3510 (conjArr 3510 (ctiG a) (ctiGi a) ctiQ3) X := by
  obtain ⟨Y, hY, hr⟩ := pow_rep htext (a := 2) (b := 6) (e := 6) (by norm_num) (by norm_num)
  exact ⟨GP a * (Y * (GP a)⁻¹), Subgroup.mul_mem _ (GP_H htext ha)
    (Subgroup.mul_mem _ hY (Subgroup.inv_mem _ (GP_H htext ha))),
    rep_compA (rep_G' htext ha).1 (rep_compA hr (rep_G' htext ha).2)⟩

theorem q_word_H {j : Nat} (hj : j < 10) :
    ∃ X ∈ fi22H 1, Rep 3510 ctiQArr[j]! X := by
  rw [ctiQArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  interval_cases j
  · exact ⟨GP 0, GP_H htext (by norm_num), (rep_G' htext (k := 0) (by norm_num)).1⟩
  · exact pow_rep htext (by norm_num) (by norm_num)
  · exact pow_rep htext (by norm_num) (by norm_num)
  · exact pow_rep htext (by norm_num) (by norm_num)
  · exact pow_rep htext (by norm_num) (by norm_num)
  · exact pow_rep htext (by norm_num) (by norm_num)
  · exact pow_rep htext (by norm_num) (by norm_num)
  · exact conj_rep htext (by norm_num)
  · exact conj_rep htext (by norm_num)
  · exact conj_rep htext (by norm_num)

theorem QP_H {j : Nat} (hj : j < 10) : QP j ∈ fi22H 1 := by
  obtain ⟨X, hX, hr⟩ := q_word_H htext hj
  rw [ctiQArr_get htext hj] at hr
  rw [(rep_Q hj).1.unique hr]
  exact hX

theorem QP_P
    {j : Nat} (hj : j < 10) : QP j ∈ fi22P := H1_le_P (QP_H htext hj)

end Members

noncomputable def ZP : Equiv.Perm (Fin 3510) := QP 6 * QP 2 * (QP 6)⁻¹ * (QP 2)⁻¹

theorem rep_Z (htext : fi22Cent3510Text = Fi22E2065.textP) : Rep 3510 ctiZ ZP := by
  have h6 := rep_Q (j := 6) (by norm_num)
  have h2 := rep_Q (j := 2) (by norm_num)
  rw [ctiZ, (ctiQ_inv htext (j := 6) (by norm_num)).1, (ctiQ_inv htext (j := 2) (by norm_num)).1,
    ctiQArr_get htext (j := 6) (by norm_num), ctiQArr_get htext (j := 2) (by norm_num)]
  have h := rep_compA h6.1 (rep_compA h2.1 (rep_compA h6.2 h2.2))
  simpa only [ZP, mul_assoc] using h

theorem rep_Z20 (htext : fi22Cent3510Text = Fi22E2065.textP) : Rep 3510 (unpack 3510 12 (Q 20)) ZP :=
  ctiZ_eq htext ▸ rep_Z htext

theorem ZP_P
    (htext : fi22Cent3510Text = Fi22E2065.textP) : ZP ∈ fi22P :=
  fi22P.mul_mem (fi22P.mul_mem (fi22P.mul_mem (QP_P htext (by norm_num)) (QP_P htext (by norm_num)))
    (fi22P.inv_mem (QP_P htext (by norm_num)))) (fi22P.inv_mem (QP_P htext (by norm_num)))

theorem apply_of_rep {P : Nat} {G : Equiv.Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 P) G)
    {x : Nat} (hx : x < 3510) : (G ⟨x, hx⟩ : Nat) = pg 12 (mask 12) P x := by
  rw [← h ⟨x, hx⟩, unpack_get' hx]

theorem perm_val {P : Nat} {G : Equiv.Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 P) G)
    (y : Fin 3510) : (G y : Nat) = pg 12 (mask 12) P y.val := by
  rw [← h y, unpack_get' y.2]

theorem pq_lt {j x : Nat} (hj : j < 21) (hx : x < 3510) : pq j x < 3510 := cn_lt (cnQ hj) x hx

theorem zf_lt {x : Nat} (hx : x < 3510) : zf x < 3510 := cn_lt (cnQ (j := 20) (by norm_num)) x hx

theorem gL_lt {k x : Nat} (hk : k < 9) (hx : x < 3510) : pg 12 (mask 12) (gL k) x < 3510 :=
  cn_lt (g_parts hk).1 x hx

theorem gI_lt {k x : Nat} (hk : k < 9) (hx : x < 3510) : pg 12 (mask 12) (gI k) x < 3510 :=
  cn_lt (g_parts hk).2 x hx

theorem par_get {i : Nat} (hi : i < 1024) : ctiPar[i]! = PA i := by
  rw [ctiPar, Fi22CtiT.par_eq, unpack_get' hi]
  rfl

theorem par_size : ctiPar.size = 1024 := by rw [ctiPar, Fi22CtiT.par_eq, unpack_size]

theorem lab_get {i : Nat} (hi : i < 1024) : ctiLab[i]! = LA i := by
  rw [ctiLab, Fi22CtiT.lab_eq, unpack_get' hi]
  rfl

theorem nxt_get {j : Nat} (hj : j < 10240) : ctiNxt[j]! = NX j := by
  rw [ctiNxt, Fi22CtiT.nxt_eq, unpack_get' hj]
  rfl

theorem cid_get {i : Nat} (hi : i < 1024) : ctiCids[i]! = CD i := by
  rw [ctiCids, Fi22CtiT.cid_eq, unpack_get' hi]
  rfl

theorem reps_get {c : Nat} (hc : c < 512) : ctiReps[c]! = RP c := by
  rw [ctiReps, Fi22CtiT.reps_eq, unpack_get' hc]
  rfl

theorem reps_size : ctiReps.size = 512 := by rw [ctiReps, Fi22CtiT.reps_eq, unpack_size]

theorem zi_get {i : Nat} (hi : i < 1024) : ctiZi[i]! = ZI i := by
  rw [ctiZi, Fi22CtiT.zi_eq, unpack_get' hi]
  rfl

theorem row_at {i : Nat} (hi : i < 1024) : rowOK i = true := by
  have hq : i / 8 < 128 := by omega
  have h := allN_spec (rowAll (i / 8) hq) (i % 8) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 8) 8) (i % 8) = i := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [e] at h

theorem rep_at {c : Nat} (hc : c < 512) : repRow c = true := by
  have hq : c / 8 < 64 := by omega
  have h := allN_spec (repAll (c / 8) hq) (c % 8) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (c / 8) 8) (c % 8) = c := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [e] at h

theorem row_parts {i : Nat} (hi : i < 1024) :
    (i ≠ 0 → PA i < i ∧ LA i < 10) ∧ (∀ t < 6, kd i t = E i (bp t)) ∧
    (∀ k < 10, NX (i * 10 + k) < 1024 ∧ ∀ t < 6, kd (NX (i * 10 + k)) t = pq k (kd i t)) ∧
    (CD i < 512 ∧ ZI i < 1024 ∧ (∀ t < 6, kd (ZI i) t = E i (zf (bp t))) ∧ CD (ZI i) = CD i ∧
      ((∀ t < 6, kd i t = kd (RP (CD i)) t) ∨ ∀ t < 6, kd i t = E (RP (CD i)) (zf (bp t)))) ∧
    SG i < 1024 ∧ (i + 1 < 1024 → kv (SG i) < kv (SG (i + 1))) := by
  have h := row_at hi
  unfold rowOK at h
  obtain ⟨hA, hB, hC, hD, hE, hF⟩ := by simpa only [bAnd_iff] using h
  refine ⟨fun h0 => ?_, fun t ht => Nat.eq_of_beq_eq_true (allN_spec hB t ht), fun k hk => ?_,
    ?_, Nat.blt_eq ▸ hE, fun h1 => ?_⟩
  · have e : Nat.beq i 0 = false := by
      cases i with
      | zero => exact absurd rfl h0
      | succ i => rfl
    rw [e] at hA
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hA
    exact ⟨Nat.blt_eq ▸ h1, Nat.blt_eq ▸ h2⟩
  · have h1 := allN_spec hC k hk
    rw [strictB_eq'] at h1
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h1
    rw [Nat.add_eq, Nat.mul_eq] at h2 h3
    exact ⟨Nat.blt_eq ▸ h2, fun t ht => Nat.eq_of_beq_eq_true (allN_spec h3 t ht)⟩
  · rw [strictB_eq'] at hD
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hD
    rw [strictB_eq'] at h2
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
    obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h6
    unfold inCo at h8
    rw [bOr_iff] at h8
    refine ⟨Nat.blt_eq ▸ h1, Nat.blt_eq ▸ h3, fun t ht => Nat.eq_of_beq_eq_true (allN_spec h5 t ht),
      Nat.eq_of_beq_eq_true h7, ?_⟩
    rcases h8 with h8 | h8
    · exact Or.inl fun t ht => Nat.eq_of_beq_eq_true (allN_spec h8 t ht)
    · exact Or.inr fun t ht => Nat.eq_of_beq_eq_true (allN_spec h8 t ht)
  · have hb : Nat.blt (Nat.add i 1) 1024 = true := Eq.mpr Nat.blt_eq h1
    rw [hb] at hF
    exact Nat.blt_eq ▸ hF

theorem rep_parts {c : Nat} (hc : c < 512) :
    RP c < 1024 ∧ CD (RP c) = c ∧
    (∀ j < 10, (∀ t < 6, pq j (kd (RP c) t) = E (RP c) (pq j (bp t))) ∨
      ∀ t < 6, pq j (kd (RP c) t) = E (RP c) (zf (pq j (bp t)))) ∧
    (∀ k < 9, PI k c < 512 ∧
      ((∀ t < 6, pg 12 (mask 12) (gL k) (E (RP c) (pg 12 (mask 12) (gI k) (bp t))) =
          kd (RP (PI k c)) t) ∨
        ∀ t < 6, pg 12 (mask 12) (gL k) (E (RP c) (pg 12 (mask 12) (gI k) (bp t))) =
          E (RP (PI k c)) (zf (bp t)))) := by
  have h := rep_at hc
  unfold repRow at h
  rw [strictB_eq'] at h
  obtain ⟨h1, h2, h3, h4⟩ := by simpa only [bAnd_iff] using h
  refine ⟨Nat.blt_eq ▸ h1, Nat.eq_of_beq_eq_true h2, fun j hj => ?_, fun k hk => ?_⟩
  · rcases (bOr_iff _ _).1 (allN_spec h3 j hj) with h | h
    · exact Or.inl fun t ht => Nat.eq_of_beq_eq_true (allN_spec h t ht)
    · exact Or.inr fun t ht => Nat.eq_of_beq_eq_true (allN_spec h t ht)
  · have h5 := allN_spec h4 k hk
    rw [strictB_eq'] at h5
    obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h5
    unfold inCo at h7
    rw [bOr_iff] at h7
    refine ⟨Nat.blt_eq ▸ h6, ?_⟩
    rcases h7 with h | h
    · exact Or.inl fun t ht => Nat.eq_of_beq_eq_true (allN_spec h t ht)
    · exact Or.inr fun t ht => Nat.eq_of_beq_eq_true (allN_spec h t ht)

theorem mem_parts {k j : Nat} (hk : k < 9) (hj : j < 10) : MM k j < 1024 ∧ ∀ t < 6,
    kd (MM k j) t = pg 12 (mask 12) (gL k) (pq j (pg 12 (mask 12) (gI k) (bp t))) := by
  have h := allN_spec (allN_spec memRows k hk) j hj
  rw [strictB_eq'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.blt_eq ▸ h1, fun t ht => Nat.eq_of_beq_eq_true (allN_spec h2 t ht)⟩

theorem z_base : (¬ ∀ t < 6, zf (bp t) = bp t) ∧ (∀ t < 6, zf (zf (bp t)) = bp t) ∧
    ∀ k < 9, ∀ t < 6, pg 12 (mask 12) (gL k) (zf (bp t)) = zf (pg 12 (mask 12) (gL k) (bp t)) := by
  obtain ⟨h1, h2, h3⟩ := by simpa only [bAnd_iff] using zFacts
  refine ⟨fun hall => ?_, fun t ht => Nat.eq_of_beq_eq_true (allN_spec h2 t ht),
    fun k hk t ht => Nat.eq_of_beq_eq_true (allN_spec (allN_spec h3 k hk) t ht)⟩
  obtain ⟨t, ht, hne⟩ := not_allN h1
  exact hne (by rw [hall t ht]; exact Nat.beq_refl _)

theorem rows_PA : ∀ i < 1024, 0 < i → PA i < i :=
  fun i hi h0 => ((row_parts hi).1 (by omega)).1

theorem rows_LA : ∀ i < 1024, 0 < i → LA i < 10 :=
  fun i hi h0 => ((row_parts hi).1 (by omega)).2

noncomputable def EE : Array (Array Nat) := mulTree 3510 ctiQArr ctiPar ctiLab

theorem E_eq (htext : fi22Cent3510Text = Fi22E2065.textP) :
    EE = Array.ofFn (n := 1024) fun i => Array.ofFn (n := 3510) fun z => E i z.val :=
  mulTree_eq (gs := 10) (fun _ hk => ctiQArr_get htext hk)
    (fun _ hk x hx => pq_lt (by omega) hx) par_size (by norm_num)
    (fun i hi h0 => ⟨par_get hi, rows_PA i hi h0⟩) (fun i hi h0 => ⟨lab_get hi, rows_LA i hi h0⟩)

theorem E_size (htext : fi22Cent3510Text = Fi22E2065.textP) : EE.size = 1024 := by
  rw [E_eq htext]
  simp

theorem E_get (htext : fi22Cent3510Text = Fi22E2065.textP) {i z : Nat} (hi : i < 1024)
    (hz : z < 3510) : (EE[i]!)[z]! = E i z := by
  rw [E_eq htext, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_ofFn_nat _ hz]

theorem E_lt {i z : Nat} (hi : i < 1024) (hz : z < 3510) : E i z < 3510 :=
  ev_lt rows_PA rows_LA (fun _ hk x hx => pq_lt (by omega) hx) _ _ _ hi hz

theorem E_succ {i z : Nat} (hi : i < 1024) (h0 : 0 < i) :
    E i z = pq (LA i) (E (PA i) z) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hp := rows_PA (j + 1) hi h0
  unfold E
  rw [ev_succ, ev_fuel rows_PA 1023 1024 (PA (j + 1)) z (by omega) (by omega) (by omega)]
  rfl

theorem kd_eq {i t : Nat} (hi : i < 1024) (ht : t < 6) : kd i t = E i (bp t) :=
  (row_parts hi).2.1 t ht

theorem rep_of_E (htext : fi22Cent3510Text = Fi22E2065.textP) {i : Nat} (hi : i < 1024)
    {X : Equiv.Perm (Fin 3510)} (h : ∀ z : Fin 3510, E i z.val = (X z : Nat)) :
    Rep 3510 EE[i]! X := fun z => by
  rw [E_get htext hi z.2]
  exact h z

theorem E_zero (z : Nat) : E 0 z = z := by
  unfold E
  exact ev_zero _ _

theorem EE_zero (htext : fi22Cent3510Text = Fi22E2065.textP) : Rep 3510 EE[0]! 1 :=
  rep_of_E htext (by norm_num) fun z => E_zero z.val

theorem EE_succ (htext : fi22Cent3510Text = Fi22E2065.textP) {i : Nat} (hi : i < 1024)
    (h0 : 0 < i) {Y : Equiv.Perm (Fin 3510)} (hYr : Rep 3510 EE[PA i]! Y) :
    Rep 3510 EE[i]! (QP (LA i) * Y) := by
  have hp := rows_PA i hi h0
  have hl := rows_LA i hi h0
  refine rep_of_E htext hi fun x => ?_
  have h1 : E (PA i) x = (Y x : Nat) := by
    rw [← E_get htext (lt_trans hp hi) x.2]
    exact hYr x
  rw [E_succ hi h0, h1, Equiv.Perm.mul_apply, perm_val (rep_Q hl).1]
  rfl

theorem E_rep
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    ∀ i < 1024, ∃ X ∈ fi22P, Rep 3510 EE[i]! X := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · refine ⟨1, fi22P.one_mem, rep_of_E htext hi fun z => ?_⟩
      rw [h0, E_zero]
      rfl
    · have hp := rows_PA i hi h0
      obtain ⟨Y, hY, hYr⟩ := ih _ hp (lt_trans hp hi)
      exact ⟨QP (LA i) * Y, fi22P.mul_mem (QP_P htext (rows_LA i hi h0)) hY,
        EE_succ htext hi h0 hYr⟩

theorem E_base (htext : fi22Cent3510Text = Fi22E2065.textP) {i : Nat} (hi : i < 1024)
    {X : Equiv.Perm (Fin 3510)} (hX : Rep 3510 EE[i]! X) {x : Nat} (hx : x < 3510) :
    (X ⟨x, hx⟩ : Nat) = E i x := by
  rw [← hX ⟨x, hx⟩, E_get htext hi hx]

theorem E_base' (htext : fi22Cent3510Text = Fi22E2065.textP) {i : Nat} (hi : i < 1024)
    {X : Equiv.Perm (Fin 3510)} (hX : Rep 3510 EE[i]! X) (y : Fin 3510) : (X y : Nat) = E i y.val := by
  rw [← hX y, E_get htext hi y.2]

section Conj

variable (htext : fi22Cent3510Text = Fi22E2065.textP)
include htext

theorem cl0 : eqA 3510 EE[0]! (idA 3510) = true := (eqA_iff (EE_zero htext) rep_idA).2 rfl

theorem cl1 {i : Nat} (hi : i < 1024) (h0 : i ≠ 0) :
    eqA 3510 EE[i]! (compA 3510 ctiQArr[ctiLab[i]!]! EE[ctiPar[i]!]!) = true := by
  obtain ⟨hp, hl⟩ := (row_parts hi).1 h0
  rw [par_get hi, lab_get hi]
  refine eqA_of_get fun z hz => ?_
  rw [E_get htext hi hz, compA_get hz, E_get htext (lt_trans hp hi) hz, ctiQArr_get htext hl,
    unpack_get' (E_lt (lt_trans hp hi) hz), E_succ hi (by omega)]
  rfl

theorem cl2
    {i k : Nat} (hi : i < 1024) (hk : k < 10) :
    eqA 3510 EE[NX (i * 10 + k)]! (compA 3510 ctiQArr[k]! EE[i]!) = true := by
  obtain ⟨hn, hb⟩ := (row_parts hi).2.2.1 k hk
  obtain ⟨Xn, hXn, hrn⟩ := E_rep htext _ hn
  obtain ⟨Xi, hXi, hri⟩ := E_rep htext i hi
  have hgk : Rep 3510 ctiQArr[k]! (QP k) := by
    rw [ctiQArr_get htext hk]
    exact (rep_Q hk).1
  refine (eqA_iff hrn (rep_compA hgk hri)).2
    (sepP hXn (fi22P.mul_mem (QP_P htext hk) hXi) fun t ht => ?_)
  rw [E_base htext hn hrn, ← kd_eq hn ht, hb t ht, kd_eq hi ht, Equiv.Perm.mul_apply,
    perm_val (rep_Q hk).1, E_base' htext hi hri, Fin.val_mk]
  all_goals rfl

theorem closure_ok :
    closureOK 3510 ctiQArr EE ctiPar ctiLab ctiNxt = true := by
  unfold closureOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [ctiQArr_size, E_size htext]
  refine ⟨⟨⟨by norm_num, cl0 htext⟩, allLt_iff.2 fun i hi => ?_⟩,
    allLt_iff.2 fun i hi => allLt_iff.2 fun k hk => ?_⟩
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h0 : i = 0
    · exact Or.inl h0
    right
    obtain ⟨hp, hl⟩ := (row_parts hi).1 h0
    refine ⟨⟨by rw [par_get hi]; exact hp, by rw [lab_get hi]; exact hl⟩, cl1 htext hi h0⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    obtain ⟨hn, -⟩ := (row_parts hi).2.2.1 k hk
    rw [nxt_get (by omega)]
    exact ⟨hn, cl2 htext hi hk⟩

theorem keyAt_eq {i : Nat} (hi : i < 1024) : keyAt 3510 [0, 1, 2, 3, 6, 4] EE[i]! = kv i := by
  have h : ∀ t < 6, (EE[i]!)[bp t]! = kd i t := fun t ht => by
    rw [E_get htext hi (bp_lt ht), kd_eq hi ht]
  have e0 : (EE[i]!)[0]! = kd i 0 := h 0 (by norm_num)
  have e1 : (EE[i]!)[1]! = kd i 1 := h 1 (by norm_num)
  have e2 : (EE[i]!)[2]! = kd i 2 := h 2 (by norm_num)
  have e3 : (EE[i]!)[3]! = kd i 3 := h 3 (by norm_num)
  have e4 : (EE[i]!)[6]! = kd i 4 := h 4 (by norm_num)
  have e5 : (EE[i]!)[4]! = kd i 5 := h 5 (by norm_num)
  simp only [keyAt, List.foldr_cons, List.foldr_nil, e0, e1, e2, e3, e4, e5]
  rfl

theorem keys_ok : keysOK 3510 [0, 1, 2, 3, 6, 4] EE = true := by
  apply keysOK_of_nodup
  have hsz := E_size htext
  have hl : (EE.toList.map (keyAt 3510 [0, 1, 2, 3, 6, 4])) =
      List.ofFn (n := 1024) fun i => kv i.val := by
    apply List.ext_getElem
    · rw [List.length_map, Array.length_toList, hsz, List.length_ofFn]
    · intro k h1 h2
      have hk : k < 1024 := by
        rw [List.length_ofFn] at h2
        exact h2
      rw [List.getElem_map, Array.getElem_toList, List.getElem_ofFn, ← getElem!_pos EE k (by omega),
        keyAt_eq htext hk]
  rw [hl]
  refine List.nodup_ofFn.2 fun i j hij => Fin.ext ?_
  exact inj_of_sorted (N := 1024) (fun m hm => (row_parts hm).2.2.2.2.1)
    (fun m hm => (row_parts (by omega : m < 1024)).2.2.2.2.2 hm) i i.2 j j.2 hij

theorem sift_ok {j : Nat} (hj : j < 10) :
    siftA 3510 (rawLevels 3510 (fi22CentStrong 1) #[0, 1, 2, 3, 6, 4]) #[0, 1, 2, 3, 6, 4] 0
      ctiQArr[j]! = true := by
  rw [ctiQArr_get htext hj]
  exact (siftA_iff_mem_fi22H (c := 1) (by norm_num) (rep_Q hj).1).2 (QP_H htext hj)

omit htext in
theorem conj_base {k : Nat} (hk : k < 9) {a : Array Nat} {X : Equiv.Perm (Fin 3510)}
    (ha : Rep 3510 a X) {t : Nat} (ht : t < 6) :
    ((GP k * X * (GP k)⁻¹) ⟨bp t, bp_lt ht⟩ : Nat) =
      pg 12 (mask 12) (gL k) (a[pg 12 (mask 12) (gI k) (bp t)]!) := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_val (rep_G hk).1, ← ha,
    perm_val (rep_G hk).2]

theorem mem_ok
    {k j : Nat} (hk : k < 9) (hj : j < 10) :
    ctiMem EE (conjArr 3510 (ctiG k) (ctiGi k) ctiQArr[j]!) = true := by
  obtain ⟨hm, hb⟩ := mem_parts hk hj
  unfold ctiMem
  refine Array.any_eq_true.2 ⟨MM k j, by rw [E_size htext]; exact hm, ?_⟩
  obtain ⟨Xm, hXm, hrm⟩ := E_rep htext _ hm
  have hq : Rep 3510 ctiQArr[j]! (QP j) := by
    rw [ctiQArr_get htext hj]
    exact (rep_Q hj).1
  have hc : Rep 3510 (conjArr 3510 (ctiG k) (ctiGi k) ctiQArr[j]!) (GP k * QP j * (GP k)⁻¹) := by
    unfold conjArr
    have := rep_compA (rep_G' htext hk).1 (rep_compA hq (rep_G' htext hk).2)
    simpa only [mul_assoc] using this
  rw [← getElem!_pos EE (MM k j) (by rw [E_size htext]; exact hm)]
  refine (eqA_iff hrm hc).2 (sepP hXm (fi22P.mul_mem (fi22P.mul_mem (GP_P htext hk) (QP_P htext hj))
    (fi22P.inv_mem (GP_P htext hk))) fun t ht => ?_)
  rw [E_base htext hm hrm, ← kd_eq hm ht, hb t ht, conj_base hk (rep_Q hj).1 ht,
    unpack_get' (gI_lt hk (bp_lt ht))]
  rfl

theorem z_ne : eqA 3510 ctiZ (idA 3510) = false := by
  cases h : eqA 3510 ctiZ (idA 3510)
  · rfl
  · exfalso
    have e := (eqA_iff (rep_Z htext) rep_idA).1 h
    apply z_base.1
    intro t ht
    have := apply_of_rep (rep_Z20 htext) (bp_lt ht)
    rw [e] at this
    exact this.symm

theorem z_sq :
    eqA 3510 (compA 3510 ctiZ ctiZ) (idA 3510) = true := by
  refine (eqA_iff (rep_compA (rep_Z htext) (rep_Z htext)) rep_idA).2
    (sepP (fi22P.mul_mem (ZP_P htext) (ZP_P htext)) fi22P.one_mem fun t ht => ?_)
  rw [Equiv.Perm.mul_apply, perm_val (rep_Z20 htext), perm_val (rep_Z20 htext),
    Equiv.Perm.one_apply, Fin.val_mk]
  exact z_base.2.1 t ht

theorem z_comm
    {k : Nat} (hk : k < 9) :
    eqA 3510 (compA 3510 (ctiG k) ctiZ) (compA 3510 ctiZ (ctiG k)) = true := by
  refine (eqA_iff (rep_compA (rep_G' htext hk).1 (rep_Z htext))
    (rep_compA (rep_Z htext) (rep_G' htext hk).1)).2
    (sepP (fi22P.mul_mem (GP_P htext hk) (ZP_P htext)) (fi22P.mul_mem (ZP_P htext) (GP_P htext hk))
      fun t ht => ?_)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_val (rep_G hk).1, perm_val (rep_Z20 htext),
    perm_val (rep_Z20 htext), perm_val (rep_G hk).1, Fin.val_mk]
  exact z_base.2.2 k hk t ht

omit htext in
theorem reps_ok : ∀ c < 512, ctiReps[c]! < 1024 ∧ ctiCids[ctiReps[c]!]! = c := by
  intro c hc
  obtain ⟨h1, h2, -⟩ := rep_parts hc
  rw [reps_get hc, cid_get h1]
  exact ⟨h1, h2⟩

theorem inCoset_ok
    {x : Array Nat} {X : Equiv.Perm (Fin 3510)} (hx : Rep 3510 x X) (hXP : X ∈ fi22P)
    {r : Nat} (hr : r < 1024) {f : Nat → Nat} (hf : ∀ t (ht : t < 6), (X ⟨bp t, bp_lt ht⟩ : Nat) = f t)
    (h : (∀ t < 6, f t = kd r t) ∨ ∀ t < 6, f t = E r (zf (bp t))) :
    ctiInCoset EE ctiZ x r = true := by
  obtain ⟨Xr, hXr, hrr⟩ := E_rep htext r hr
  unfold ctiInCoset
  rw [Bool.or_eq_true]
  rcases h with h | h
  · refine Or.inl ((eqA_iff hx hrr).2 (sepP hXP hXr fun t ht => ?_))
    rw [hf t ht, h t ht, E_base htext hr hrr, kd_eq hr ht]
  · refine Or.inr ((eqA_iff hx (rep_compA hrr (rep_Z htext))).2
      (sepP hXP (fi22P.mul_mem hXr (ZP_P htext)) fun t ht => ?_))
    rw [hf t ht, h t ht, Equiv.Perm.mul_apply, E_base' htext hr hrr, perm_val (rep_Z20 htext),
      Fin.val_mk]
    all_goals rfl

theorem coset_ok
    {i : Nat} (hi : i < 1024) :
    ctiCids[i]! < 512 ∧ ctiZi[i]! < 1024 ∧
      eqA 3510 EE[ctiZi[i]!]! (compA 3510 EE[i]! ctiZ) = true ∧ ctiCids[ctiZi[i]!]! = ctiCids[i]! ∧
      ctiInCoset EE ctiZ EE[i]! ctiReps[ctiCids[i]!]! = true := by
  obtain ⟨hc, hz, hzb, hcz, hin⟩ := (row_parts hi).2.2.2.1
  rw [cid_get hi, zi_get hi, cid_get hz, reps_get hc]
  obtain ⟨Xi, hXi, hri⟩ := E_rep htext i hi
  obtain ⟨Xy, hXy, hry⟩ := E_rep htext _ hz
  refine ⟨hc, hz, (eqA_iff hry (rep_compA hri (rep_Z htext))).2
    (sepP hXy (fi22P.mul_mem hXi (ZP_P htext)) fun t ht => ?_), hcz, ?_⟩
  · rw [E_base htext hz hry, ← kd_eq hz ht, hzb t ht, Equiv.Perm.mul_apply, E_base' htext hi hri,
      perm_val (rep_Z20 htext), Fin.val_mk]
    all_goals rfl
  · exact inCoset_ok htext hri hXi (rep_parts hc).1 (f := kd i)
      (fun t ht => by rw [E_base htext hi hri, kd_eq hi ht]) hin

theorem qcomm_ok
    {j c : Nat} (hj : j < 10) (hc : c < 512) :
    (eqA 3510 (compA 3510 ctiQArr[j]! EE[ctiReps[c]!]!) (compA 3510 EE[ctiReps[c]!]! ctiQArr[j]!) ||
      eqA 3510 (compA 3510 ctiQArr[j]! EE[ctiReps[c]!]!)
        (compA 3510 (compA 3510 EE[ctiReps[c]!]! ctiZ) ctiQArr[j]!)) = true := by
  obtain ⟨hr, -, hq, -⟩ := rep_parts hc
  rw [reps_get hc, Bool.or_eq_true]
  obtain ⟨Xr, hXr, hrr⟩ := E_rep htext _ hr
  have hqj : Rep 3510 ctiQArr[j]! (QP j) := by
    rw [ctiQArr_get htext hj]
    exact (rep_Q hj).1
  have hl : ∀ t (ht : t < 6), ((QP j * Xr) ⟨bp t, bp_lt ht⟩ : Nat) = pq j (kd (RP c) t) := by
    intro t ht
    rw [Equiv.Perm.mul_apply, perm_val (rep_Q hj).1, E_base' htext hr hrr, Fin.val_mk, kd_eq hr ht]
    all_goals rfl
  rcases hq j hj with h | h
  · refine Or.inl ((eqA_iff (rep_compA hqj hrr) (rep_compA hrr hqj)).2
      (sepP (fi22P.mul_mem (QP_P htext hj) hXr) (fi22P.mul_mem hXr (QP_P htext hj)) fun t ht => ?_))
    rw [hl t ht, h t ht, Equiv.Perm.mul_apply, E_base' htext hr hrr, perm_val (rep_Q hj).1,
      Fin.val_mk]
    all_goals rfl
  · refine Or.inr ((eqA_iff (rep_compA hqj hrr) (rep_compA (rep_compA hrr (rep_Z htext)) hqj)).2
      (sepP (fi22P.mul_mem (QP_P htext hj) hXr)
        (fi22P.mul_mem (fi22P.mul_mem hXr (ZP_P htext)) (QP_P htext hj)) fun t ht => ?_))
    rw [hl t ht, h t ht, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, E_base' htext hr hrr,
      perm_val (rep_Z20 htext), perm_val (rep_Q hj).1, Fin.val_mk]
    all_goals rfl

end Conj

theorem s5Rows : allN 12 (fun j => Nat.beq (Fi22Cti5.S j) (pg 5120 (mask 5120) Fi22CtiT.S5.F j)) =
    true := by quickRfl
theorem s5Base : allN 3 (fun t => Nat.beq ctiB5[t]! (pg 10 (mask 10) Fi22Cti5.BP t)) = true := by
  quickRfl
theorem s5Perm : allN 12 (fun j => permOK 512 10 (mask 10) (512 * 10) (Fi22Cti5.S j) (Fi22Cti5.SI j)) =
    true := by quickRfl
theorem prod5 : ((List.range 3).map fun i => rcnt (Fi22Cti5.LR i)).prod = 51840 := by
  decide +kernel

noncomputable abbrev S5 : Array (Array Nat) :=
  Array.ofFn (n := 12) fun j => unpack 512 10 (Fi22Cti5.S j.val)

theorem s5_eq : ctiS5 = S5 := by
  rw [ctiS5, Fi22CtiT.s5_eq]
  exact rowsOf_unpack (by norm_num) (by norm_num)
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec s5Rows j hj)

theorem binds5 : Binds 512 10 Fi22Cti5.S 12 3 Fi22Cti5.BP S5 ctiB5 :=
  ⟨by norm_num, by norm_num, by norm_num, by simp, fun j hj => by
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn], rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec s5Base t ht)⟩

theorem image_ok : ctiS5.size = 12 ∧ rawChainOK 512 (ctiS5.extract 0 9) ctiS5 ctiB5 ctiW5 4 = true ∧
    (rawOrbitSizes 512 ctiS5 ctiB5).prod = 51840 := by
  rw [s5_eq, Fi22CtiW.w_eq, rawOrbitSizesK_sound binds5 s5Perm Fi22Cti5.hl, prod5]
  exact ⟨by simp, rawChainK_sound (NS := 128) (CH := 4) binds5 Fi22Cti5.head Fi22Cti5.hl
    (by norm_num) Fi22Cti5.hs, rfl⟩

theorem pis_row {k : Nat} (hk : k < 9) : (ctiS5.extract 0 9)[k]! = unpack 512 10 (Fi22Cti5.S k) := by
  rw [s5_eq]
  have h1 : k < (S5.extract 0 9).size := by simp; omega
  have h2 : k < S5.size := by simp; omega
  have h : (S5.extract 0 9)[k]! = S5[k]! := by
    rw [getElem!_pos _ k h1, getElem!_pos S5 k h2]
    simp [Array.getElem_extract]
  rw [h, getElem!_pos S5 k h2, Array.getElem_ofFn]

theorem pis_get {k c : Nat} (hk : k < 9) (hc : c < 512) : ((ctiS5.extract 0 9)[k]!)[c]! = PI k c := by
  rw [pis_row hk, unpack_get' hc, Nat.eq_of_beq_eq_true (allN_spec s5Rows k (by omega)), pg_row hc]
  unfold PI
  rw [Nat.add_eq, Nat.mul_eq, Nat.mul_comm]

theorem pis_size {k : Nat} (hk : k < 9) : ((ctiS5.extract 0 9)[k]!).size = 512 := by
  rw [pis_row hk, unpack_size]

theorem pis_count : (ctiS5.extract 0 9).size = 9 := by
  rw [s5_eq]
  simp

theorem pi_ok
    (htext : fi22Cent3510Text = Fi22E2065.textP) {k c : Nat} (hk : k < 9) (hc : c < 512) :
    ((ctiS5.extract 0 9)[k]!)[c]! < 512 ∧
      ctiInCoset EE ctiZ (conjArr 3510 (ctiG k) (ctiGi k) EE[ctiReps[c]!]!)
        ctiReps[((ctiS5.extract 0 9)[k]!)[c]!]! = true := by
  obtain ⟨hr, -, -, hp⟩ := rep_parts hc
  obtain ⟨hlt, hin⟩ := hp k hk
  rw [pis_get hk hc, reps_get hc, reps_get hlt]
  refine ⟨hlt, ?_⟩
  obtain ⟨Xr, hXr, hrr⟩ := E_rep htext _ hr
  have hconj : Rep 3510 (conjArr 3510 (ctiG k) (ctiGi k) EE[RP c]!) (GP k * Xr * (GP k)⁻¹) := by
    unfold conjArr
    have := rep_compA (rep_G' htext hk).1 (rep_compA hrr (rep_G' htext hk).2)
    simpa only [mul_assoc] using this
  refine inCoset_ok htext hconj (fi22P.mul_mem (fi22P.mul_mem (GP_P htext hk) hXr)
    (fi22P.inv_mem (GP_P htext hk))) (rep_parts hlt).1
    (f := fun t => pg 12 (mask 12) (gL k) (E (RP c) (pg 12 (mask 12) (gI k) (bp t))))
    (fun t ht => ?_) hin
  rw [conj_base hk hrr ht, E_get htext hr (gI_lt hk (bp_lt ht))]

theorem qok
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    ctiQOK (mulTree 3510 ctiQArr ctiPar ctiLab) ctiPar ctiLab ctiNxt ctiCids ctiReps ctiZi
      (ctiS5.extract 0 9) = true := by
  unfold ctiQOK
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨closure_ok htext, E_size htext⟩, keys_ok htext⟩,
    allLt_iff.2 fun j hj => sift_ok htext hj⟩,
    allLt_iff.2 fun k hk => allLt_iff.2 fun j hj => mem_ok htext hk hj⟩, z_ne htext⟩,
    z_sq htext⟩, allLt_iff.2 fun k hk => z_comm htext hk⟩, reps_size⟩, pis_count⟩,
    allLt_iff.2 fun c hc => ?_⟩, allLt_iff.2 fun i hi => ?_⟩,
    allLt_iff.2 fun j hj => allLt_iff.2 fun c hc => qcomm_ok htext hj hc⟩,
    allLt_iff.2 fun k hk => ?_⟩, allLt_iff.2 fun j hj => ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact reps_ok c hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    obtain ⟨a, b, c, d, e⟩ := coset_ok htext hi
    exact ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩
  · simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨pis_size hk, allLt_iff.2 fun c hc => ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact pi_ok htext hk hc
  · rw [(ctiQ_inv htext hj).1]
    exact (ctiQ_inv htext hj).2

end CertificateChecks.KernelSpor.Fi22CtiA

end
