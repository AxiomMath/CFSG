
module

public import Certificates.Kernel.SporSch.HN.Pt2109
public import Certificates.Kernel.SporSch.HN.Pt2108K
public import Certificates.Kernel.SporSch.HN.Pt2108KM
public import Certificates.Kernel.SporSch.HN.Pt2108G0
public import Certificates.Kernel.SporSch.HN.Pt2108N
public import CFSG.Sporadic.HNSchreier.SylowCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPt2108

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KC.LL.HNXT4 CFSG.KC.LL.HNXSyl CFSG.KS
open CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord CFSG.KS.EnumBase
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNArrS
open CertificateChecks.KernelSporSch.HNPt2103 CertificateChecks.KernelSporSch.HNPt2109
open CFSG.KD.HNPt2108 Matrix

local notation "OM'" => ordMat 5 133 13 1729

theorem sb_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem ba_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bi_eq (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by cases c <;> rfl

noncomputable abbrev PG (j : ℕ) : JH :=
  if j < 5 then ((FAData.pLift[j]!).map fun l => C3J (l - 1)).prod else wJ sL FAData.pKernel

theorem foldl_arrJ (c3 : ℕ → JH) : ∀ (w : List ℕ) (g : JH),
    w.foldl (fun acc l => pcomp nPts acc (Array.ofFn (n := 7) fun j => arrJ (c3 j.val))[l - 1]!)
      (arrJ g) = arrJ (g * (w.map fun l => c3 (l - 1)).prod) ∨ ∃ l ∈ w, ¬ (1 ≤ l ∧ l ≤ 7)
  | [], g => Or.inl (by simp)
  | l :: w, g => by
    by_cases hl : 1 ≤ l ∧ l ≤ 7
    · rcases foldl_arrJ c3 w (g * c3 (l - 1)) with h | ⟨l', hl', h'⟩
      · left
        rw [List.foldl_cons, getElem!_pos _ (l - 1) (by simp; omega), Array.getElem_ofFn,
          pcomp_arrJ, h, List.map_cons, List.prod_cons, mul_assoc]
      · exact Or.inr ⟨l', List.mem_cons_of_mem _ hl', h'⟩
    · exact Or.inr ⟨l, List.mem_cons_self, hl⟩

theorem lift_arrJ {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 7) :
    w.foldl (fun acc l => pcomp nPts acc (Array.ofFn (n := 7) fun j => arrJ (C3J j.val))[l - 1]!)
      (pid nPts) = arrJ (w.map fun l => C3J (l - 1)).prod := by
  rw [pid_arrJ]
  rcases foldl_arrJ C3J w 1 with h | ⟨l, hl, h'⟩
  · rw [h, one_mul]
  · exact absurd (hw l hl) h'

theorem G_eq :
    (FAData.pLift.map fun lw => lw.foldl (fun acc l =>
      pcomp nPts acc (Array.ofFn (n := 7) fun j => arrJ (C3J j.val))[l - 1]!) (pid nPts)).push
      (pword nPts SJ (pinvs nPts SJ) FAData.pKernel) =
    Array.ofFn (n := 6) fun j => arrJ (PG j.val) := by
  obtain ⟨hs, hl, hk⟩ := lift_data
  refine Array.ext (by simp [hs]) fun j h1 h2 => ?_
  have hj : j < 6 := by simpa using h2
  rw [Array.getElem_ofFn]
  rcases Nat.lt_or_ge j 5 with h | h
  · rw [Array.getElem_push_lt (by simpa [hs] using h), Array.getElem_map,
      ← getElem!_pos FAData.pLift j (by rw [hs]; exact h), lift_arrJ (hl j h)]
    simp only [PG, if_pos h]
  · have e : j = 5 := by omega
    subst e
    rw [Array.getElem_push, dif_neg (by simp [hs]), pword_arrJ SJ_arrs _ hk]
    simp only [PG]
    rfl

theorem G_get {j : ℕ} (hj : j < 6) :
    (Array.ofFn (n := 6) fun j => arrJ (PG j.val))[j]! = arrJ (PG j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem Gi_get {j : ℕ} (hj : j < 6) :
    (pinvs nPts (Array.ofFn (n := 6) fun j => arrJ (PG j.val)))[j]! = arrJ (PG j)⁻¹ := by
  rw [pinvs_get (by simpa using hj), G_get hj, pinvCand_arrJ]

noncomputable def EA : ℕ → ℕ → JH
  | 0, _ => 1
  | f + 1, i => if i = 0 then 1 else PG (FAData.pParents[i]!).2 * EA f (FAData.pParents[i]!).1

noncomputable abbrev E (i : ℕ) : JH := EA 729 i

theorem lab_lt (i : ℕ) : (FAData.pParents[i]!).2 < 6 := by
  rcases Nat.lt_or_ge i 729 with h | h
  · by_cases h0 : i = 0
    · subst h0
      rw [par_data.2.1]
      decide
    · exact (par_data.2.2 i h h0).2
  · rw [getElem!_neg _ i (by rw [par_data.1]; omega)]
    decide

theorem pev_eq : ∀ (f i x : ℕ), x < nPts →
    pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents f i x = gi (EA f i) x
  | 0, i, x, hx => by rw [pev, EA, gi_one hx]
  | f + 1, i, x, hx => by
    rw [pev, EA]
    by_cases hi : i = 0
    · rw [if_pos hi, if_pos hi, gi_one hx]
    · rw [if_neg hi, if_neg hi, pev_eq f _ x hx, G_get (lab_lt i), gi_mul _ _ hx,
        arrJ_get _ (gi_lt _ hx)]

theorem EA_stable : ∀ i < 729, ∀ f, i < f → EA f i = E i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [show E i = EA (728 + 1) i from rfl, EA, EA]
    by_cases hi0 : i = 0
    · rw [if_pos hi0, if_pos hi0]
    · rw [if_neg hi0, if_neg hi0]
      have hp := (par_data.2.2 i hi hi0).1
      rw [ih _ hp (by omega) f' (by omega), ih _ hp (by omega) 728 (by omega)]

theorem E_succ {i : ℕ} (hi : i < 729) (hi0 : i ≠ 0) :
    E i = PG (FAData.pParents[i]!).2 * E (FAData.pParents[i]!).1 := by
  have hp := (par_data.2.2 i hi hi0).1
  rw [show E i = EA (728 + 1) i from rfl, EA, if_neg hi0, EA_stable _ (by omega) 728 (by omega)]

theorem E_zero : E 0 = 1 := by
  rw [show E 0 = EA (728 + 1) 0 from rfl, EA, if_pos rfl]

theorem C3S_eq : C3S = C3W := rfl

theorem scodeK_eq : scodeK = scode := rfl

theorem liftM_mat : ∀ (w : List ℕ), (∀ l ∈ w, 1 ≤ l ∧ l ≤ 7) →
    ∀ {A : ℕ} {g : JH}, Canon 5 133 13 A → OM' A = matJ g →
    Canon 5 133 13 (w.foldl (fun acc l => CFSG.KC.LL.HN.mm acc (C3S (l - 1))) A) ∧
      OM' (w.foldl (fun acc l => CFSG.KC.LL.HN.mm acc (C3S (l - 1))) A) =
        matJ (g * (w.map fun l => C3J (l - 1)).prod)
  | [], _, A, g, hA, hg => by simpa using ⟨hA, hg⟩
  | l :: w, hw, A, g, hA, hg => by
    obtain ⟨c1, c2⟩ := C3_mat (j := l - 1) (by have := hw l List.mem_cons_self; omega)
    rw [← C3S_eq] at c1 c2
    have hm := HNXP.mm_sound hA c1
    have ih := liftM_mat w (fun z hz => hw z (List.mem_cons_of_mem _ hz)) hm.1
      (by rw [hm.2, hg, c2, ← matJ_mul])
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih

theorem GM_mat {j : ℕ} (hj : j < 6) :
    Canon 5 133 13 (GMf j) ∧ OM' (GMf j) = matJ (PG j) := by
  have h := g_ok
  simp only [ba_eq, Bool.and_eq_true] at h
  obtain ⟨h5, hk⟩ := h
  obtain ⟨-, hl, hkl⟩ := lift_data
  rcases Nat.lt_or_ge j 5 with h | h
  · rw [Nat.eq_of_beq_eq_true (allN_spec h5 j h)]
    have := liftM_mat _ (hl j h) (one_sound CFSG.KD.OrdHN.consts).1
      (by rw [HNXP.one_ord, ← matJ_one])
    rw [one_mul] at this
    simp only [PG, if_pos h]
    exact this
  · obtain rfl : j = 5 := by omega
    simp only [PG, if_neg (by norm_num : ¬ (5 < 5))]
    exact strong_elem (Nat.eq_of_beq_eq_true hk).symm (by rw [scodeK_eq]) hkl

theorem EM_mat : ∀ f i, Canon 5 133 13 (emat GMf PARf LABf f i) ∧
    OM' (emat GMf PARf LABf f i) = matJ (EA f i)
  | 0, i => ⟨(one_sound CFSG.KD.OrdHN.consts).1, by
      change OM' CFSG.KD.OrdHN.ONE = matJ (EA 0 i)
      rw [HNXP.one_ord, EA, matJ_one]⟩
  | f + 1, i => by
    by_cases hi : i = 0
    · subst hi
      refine ⟨(one_sound CFSG.KD.OrdHN.consts).1, ?_⟩
      change OM' CFSG.KD.OrdHN.ONE = matJ (EA (f + 1) 0)
      rw [HNXP.one_ord, EA, if_pos rfl, matJ_one]
    · have e : emat GMf PARf LABf (f + 1) i =
          CFSG.KC.LL.HN.mm (GMf (LABf i)) (emat GMf PARf LABf f (PARf i)) := by
        change nIf(Nat.beq i 0, _, _) = _
        rw [show Nat.beq i 0 = false from
          Bool.eq_false_iff.mpr fun e => hi (Nat.eq_of_beq_eq_true e)]
        rfl
      rw [e]
      obtain ⟨c1, m1⟩ := GM_mat (j := LABf i) (lab_lt i)
      obtain ⟨c2, m2⟩ := EM_mat f (PARf i)
      have hm := HNXP.mm_sound c1 c2
      refine ⟨hm.1, ?_⟩
      rw [hm.2, m1, m2, ← matJ_mul, EA, if_neg hi]
      rfl

noncomputable abbrev Om (t : ℕ) : ℕ := f21 OM t

theorem om_bound {t : ℕ} (ht : t < 15312) : Om t < nPts := by
  have h := om_lt
  simp only [ba_eq, Bool.and_eq_true] at h
  exact Nat.blt_eq.mp (allN_spec h.2 t ht)

theorem sg_bound {j t : ℕ} (hj : j < 6) (ht : t < 15312) : f14 (SGf j) t < 15312 :=
  Nat.blt_eq.mp (allN_spec (allN_spec sg_lt j hj) t ht)

theorem pt_img {j t : ℕ} (hj : j < 6) (ht : t < 15312) :
    gi (PG j) (Om t) = Om (f14 (SGf j) t) := by
  obtain ⟨cW, mW⟩ := GM_mat hj
  have hs : 15 * j + t / 1024 < 90 := by omega
  have h := pK.all _ hs
  unfold pS at h
  rw [sb_eq, sb_eq,
    show Nat.div (15 * j + t / 1024) 15 = j by change (15 * j + t / 1024) / 15 = j; omega,
    show Nat.mod (15 * j + t / 1024) 15 = t / 1024 by change (15 * j + t / 1024) % 15 = t / 1024; omega] at h
  have hn : nIf(Nat.blt (t / 1024) 14, 1024, 976) = if t / 1024 < 14 then 1024 else 976 := by
    by_cases hc : t / 1024 < 14
    · rw [if_pos hc, show Nat.blt (t / 1024) 14 = true from Nat.blt_eq.mpr hc]
    · rw [if_neg hc, show Nat.blt (t / 1024) 14 = false from
        Bool.eq_false_iff.mpr fun e => hc (Nat.blt_eq.mp e)]
  rw [hn] at h
  have hk : t % 1024 < if t / 1024 < 14 then 1024 else 976 := by split_ifs <;> omega
  have hb : ∀ k < (if t / 1024 < 14 then 1024 else 976), Nat.add (Nat.mul 1024 (t / 1024)) k < 15312 := by
    intro k hk'
    change 1024 * (t / 1024) + k < 15312
    split_ifs at hk' <;> omega
  have e := gi_fn cW mW h (fun k hk' => ⟨om_bound (hb k hk'), om_bound (sg_bound hj (hb k hk'))⟩) hk
  have et : Nat.add (Nat.mul 1024 (t / 1024)) (t % 1024) = t := Nat.div_add_mod t 1024
  simp only [et] at e
  exact e

theorem base_get {k : ℕ} (hk : k < 22) : Om k = g0 Data.baseList k := by
  have h := allN_spec v0 k hk
  simp only [ba_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2

noncomputable abbrev Vr (i k : ℕ) : ℕ := f14 (VRf i) k

noncomputable abbrev Wr (i k : ℕ) : ℕ := f14 (WRf i) k

theorem rowK_spec {SG R PAR LAB : ℕ → ℕ} {len i : ℕ} (h : rowK SG R PAR LAB len i = true) :
    ∀ k < len, f14 (R i) k = f14 (SG (LAB i)) (f14 (R (PAR i)) k) := by
  unfold rowK at h
  simp only [sb_eq] at h
  exact fun k hk => Nat.eq_of_beq_eq_true (allN_spec h k hk)

theorem imgK_spec {SG R : ℕ → ℕ} {len j a b : ℕ} (h : HNXSyl.imgK SG R len j a b = true) :
    ∀ k < len, f14 (R a) k = f14 (SG j) (f14 (R b) k) := by
  unfold HNXSyl.imgK at h
  simp only [sb_eq] at h
  exact fun k hk => Nat.eq_of_beq_eq_true (allN_spec h k hk)

theorem blockK_spec {SG V W : ℕ → ℕ} {len j a b : ℕ} (h : blockK SG V W len j a b = true) :
    ∀ k < len, f14 (V a) k = f14 (SG j) (f14 (W b) (len * j + k)) := by
  unfold blockK at h
  simp only [sb_eq] at h
  exact fun k hk => Nat.eq_of_beq_eq_true (allN_spec h k hk)

theorem slice61 {f : ℕ → Bool} (h : ∀ s < 12, (allN 61 fun d => strictB (Nat.add (Nat.add
    (Nat.mul 61 s) d) 1) fun i => bIf(Nat.blt i 729, f i, true)) = true) :
    ∀ i < 729, i ≠ 0 → f i = true := by
  intro i hi h0
  have hs := allN_spec (h ((i - 1) / 61) (by omega)) ((i - 1) % 61) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.add (Nat.mul 61 ((i - 1) / 61)) ((i - 1) % 61)) 1 = i := by
    change 61 * ((i - 1) / 61) + (i - 1) % 61 + 1 = i
    omega
  rw [sb_eq, e, bi_eq, if_pos (Nat.blt_eq.mpr hi)] at hs
  exact hs

theorem v_lt {i k : ℕ} (hi : i < 729) (hk : k < 22) : Vr i k < 15312 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h0 : i = 0
    · subst h0
      have h := allN_spec v0 k hk
      simp only [ba_eq, Bool.and_eq_true] at h
      rw [show Vr 0 k = k from Nat.eq_of_beq_eq_true h.1]
      omega
    · have hp : PARf i < i := (par_data.2.2 i hi h0).1
      rw [Vr, rowK_spec (slice61 (fun s hs => vK.all s hs) i hi h0) k hk]
      exact sg_bound (lab_lt i) (ih _ hp (by omega))

theorem row_V {i k : ℕ} (hi : i < 729) (hk : k < 22) :
    gi (E i) (g0 Data.baseList k) = Om (Vr i k) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h0 : i = 0
    · subst h0
      have h := allN_spec v0 k hk
      simp only [ba_eq, Bool.and_eq_true] at h
      rw [E_zero, show Vr 0 k = k from Nat.eq_of_beq_eq_true h.1, ← base_get hk,
        gi_one (om_bound (by omega))]
    · have hp := (par_data.2.2 i hi h0).1
      rw [E_succ hi h0, gi_mul _ _ (by rw [← base_get hk]; exact om_bound (by omega)),
        ih _ hp (by omega), pt_img (lab_lt i) (v_lt (by omega) hk), Vr, Vr,
        rowK_spec (slice61 (fun s hs => vK.all s hs) i hi h0) k hk]
      rfl

theorem w_lt {i k : ℕ} (hi : i < 729) (hk : k < 132) : Wr i k < 15312 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h0 : i = 0
    · subst h0
      exact Nat.blt_eq.mp (allN_spec w0_lt k hk)
    · have hp : PARf i < i := (par_data.2.2 i hi h0).1
      rw [Wr, rowK_spec (slice61 (fun s hs => wK.all s hs) i hi h0) k hk]
      exact sg_bound (lab_lt i) (ih _ hp (by omega))

theorem w0_spec {j k : ℕ} (hj : j < 6) (hk : k < 22) : f14 (SGf j) (Wr 0 (22 * j + k)) = k :=
  Nat.eq_of_beq_eq_true (allN_spec (allN_spec w0 j hj) k hk)

theorem row_W {i j k : ℕ} (hi : i < 729) (hj : j < 6)
    (hk : k < 22) : gi (E i) (gi (PG j)⁻¹ (g0 Data.baseList k)) = Om (Wr i (22 * j + k)) := by
  have hjk : 22 * j + k < 132 := by omega
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h0 : i = 0
    · subst h0
      have hw := w_lt (i := 0) (by norm_num) hjk
      have e : g0 Data.baseList k = gi (PG j) (Om (Wr 0 (22 * j + k))) := by
        rw [pt_img hj hw, w0_spec hj hk, base_get hk]
      rw [E_zero, e, gi_inv _ (om_bound hw), gi_one (om_bound hw)]
    · have hp := (par_data.2.2 i hi h0).1
      have hb : g0 Data.baseList k < nPts := by rw [← base_get hk]; exact om_bound (by omega)
      rw [E_succ hi h0, gi_mul _ _ (gi_lt _ hb), ih _ hp (by omega),
        pt_img (lab_lt i) (w_lt (by omega) hjk), Wr, Wr,
        rowK_spec (slice61 (fun s hs => wK.all s hs) i hi h0) _ hjk]
      rfl

theorem slice243 {f : ℕ → ℕ → Bool} (h : ∀ q < 18, (strictB (Nat.div q 3) fun j =>
    strictB (Nat.mod q 3) fun s => allN 243 fun d => strictB (Nat.add (Nat.mul 243 s) d) fun i =>
      f j i) = true) : ∀ j < 6, ∀ i < 729, f j i = true := by
  intro j hj i hi
  have hq := h (3 * j + i / 243) (by omega)
  have e1 : Nat.div (3 * j + i / 243) 3 = j := by change (3 * j + i / 243) / 3 = j; omega
  have e2 : Nat.mod (3 * j + i / 243) 3 = i / 243 := by change (3 * j + i / 243) % 3 = i / 243; omega
  rw [sb_eq, e1, sb_eq, e2] at hq
  have := allN_spec hq (i % 243) (Nat.mod_lt _ (by norm_num))
  rw [sb_eq, show Nat.add (Nat.mul 243 (i / 243)) (i % 243) = i from Nat.div_add_mod i 243] at this
  exact this

noncomputable abbrev bimgs : Array (List ℕ) := Array.ofFn (n := 729) fun i =>
  Data.baseList.map fun b => pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729 i.val b

theorem base_mem {b : ℕ} (hb : b ∈ Data.baseList) : ∃ k < 22, b = g0 Data.baseList k := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
  refine ⟨k, by rw [base_len] at hk; exact hk, ?_⟩
  unfold g0
  rw [List.getD_eq_getElem _ _ hk]

theorem base_lt {k : ℕ} (hk : k < 22) : g0 Data.baseList k < nPts := by
  rw [← base_get hk]
  exact om_bound (by omega)

theorem pev_base {i k : ℕ} (hi : i < 729) (hk : k < 22) :
    pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729 i (g0 Data.baseList k) =
      Om (Vr i k) := by
  rw [pev_eq _ _ _ (base_lt hk)]
  exact row_V hi hk

theorem bimgs_get {i : ℕ} (hi : i < 729) : bimgs[i]! = Data.baseList.map fun b =>
    pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729 i b := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem left_ok {j i : ℕ} (hj : j < 6) (hi : i < 729) :
    bimgs[(FAData.pLeft[j]!)[i]!]! = Data.baseList.map fun b =>
      ((Array.ofFn (n := 6) fun j => arrJ (PG j.val))[j]!)[pev (Array.ofFn (n := 6) fun j =>
        arrJ (PG j.val)) FAData.pParents 729 i b]! := by
  have hL := (left_data j hj).2 i hi
  rw [bimgs_get hL]
  refine List.map_congr_left fun b hb => ?_
  obtain ⟨k, hk, rfl⟩ := base_mem hb
  rw [pev_base hL hk, pev_base hi hk, G_get hj, arrJ_get _ (om_bound (v_lt hi hk)),
    pt_img hj (v_lt hi hk)]
  have h := imgK_spec (slice243 (fun q hq => lK.all q hq) j hj i hi) k hk
  rw [Lf_eq] at h
  exact congrArg Om h

theorem conj_ok {j i : ℕ} (hj : j < 6) (hi : i < 729) :
    bimgs[(SylowData.conj[j]!)[i]!]! = Data.baseList.map fun b =>
      ((Array.ofFn (n := 6) fun j => arrJ (PG j.val))[j]!)[pev (Array.ofFn (n := 6) fun j =>
        arrJ (PG j.val)) FAData.pParents 729 i
        ((pinvs nPts (Array.ofFn (n := 6) fun j => arrJ (PG j.val)))[j]!)[b]!]! := by
  have hC := (conj_data j hj).2 i hi
  rw [bimgs_get hC]
  refine List.map_congr_left fun b hb => ?_
  obtain ⟨k, hk, rfl⟩ := base_mem hb
  have hw := w_lt hi (show 22 * j + k < 132 by omega)
  rw [pev_base hC hk, Gi_get hj, arrJ_get _ (base_lt hk),
    pev_eq _ _ _ (gi_lt _ (base_lt hk)), row_W hi hj hk, G_get hj, arrJ_get _ (om_bound hw),
    pt_img hj hw]
  have h := blockK_spec (slice243 (fun q hq => cK.all q hq) j hj i hi) k hk
  rw [Cf_eq] at h
  exact congrArg Om h

theorem dist_ok {i k : ℕ} (hi : i < 729) (hk : k < 729) (hik : i < k) :
    bimgs[i]! ≠ bimgs[k]! := by
  intro e
  rw [bimgs_get hi, bimgs_get hk] at e
  have e0 := congrArg (fun l => l.getD 0 0) e
  have e1 := congrArg (fun l => l.getD 1 0) e
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at e0 e1
  have b0 : Data.baseList[0]? = some (g0 Data.baseList 0) := rfl
  have b1 : Data.baseList[1]? = some (g0 Data.baseList 1) := rfl
  rw [b0] at e0
  rw [b1] at e1
  simp only [Option.map_some, Option.getD_some] at e0 e1
  rw [pev_base hi (by norm_num), pev_base hk (by norm_num)] at e0
  rw [pev_base hi (by norm_num), pev_base hk (by norm_num)] at e1
  have ki := Nat.eq_of_beq_eq_true (allN_spec key i hi)
  have kk := Nat.eq_of_beq_eq_true (allN_spec key k hk)
  have hk61 : k / 61 < 12 := by omega
  have hd := allN_spec (dK.all (k / 61) hk61) (k % 61) (Nat.mod_lt _ (by norm_num))
  rw [sb_eq, show Nat.add (Nat.mul 61 (k / 61)) (k % 61) = k from Nat.div_add_mod k 61, bi_eq,
    if_pos (Nat.blt_eq.mpr hk)] at hd
  have := allN_spec hd i hik
  rw [Bool.not_eq_true', ki, kk] at this
  change (Nat.beq (Om (Vr k 0) + 2097152 * Om (Vr k 1)) (Om (Vr i 0) + 2097152 * Om (Vr i 1))) = false
    at this
  rw [← e0, ← e1, Nat.beq_refl] at this
  exact absurd this (by decide)

theorem memL_eq : ∀ (l : List ℕ) (x : ℕ), memL l x = l.contains x
  | [], _ => rfl
  | a :: l, x => by
    change bIf(Nat.beq a x, true, memL l x) = (a :: l).contains x
    rw [bi_eq, memL_eq l x, List.contains_cons]
    by_cases h : a = x
    · subst h
      simp
    · rw [if_neg (fun e => h (Nat.eq_of_beq_eq_true e))]
      simp [Ne.symm h]

theorem cub_get {i : ℕ} (hi : i < 729) : cub i = true := by
  have h27 : i / 27 < 27 := by omega
  have := allN_spec (qK.all (i / 27) h27) (i % 27) (Nat.mod_lt _ (by norm_num))
  rwa [show Nat.add (Nat.mul 27 (i / 27)) (i % 27) = i from Nat.div_add_mod i 27] at this

theorem cube_mat (i : ℕ) :
    Canon 5 133 13 (CFSG.KC.LL.HN.mm (EM i) (CFSG.KC.LL.HN.mm (EM i) (EM i))) ∧
      OM' (CFSG.KC.LL.HN.mm (EM i) (CFSG.KC.LL.HN.mm (EM i) (EM i))) = matJ (E i * (E i * E i)) := by
  obtain ⟨c, m⟩ := EM_mat 729 i
  have h1 := HNXP.mm_sound c c
  have h2 := HNXP.mm_sound c h1.1
  refine ⟨h2.1, ?_⟩
  change OM' (CFSG.KC.LL.HN.mm (emat GMf PARf LABf 729 i)
    (CFSG.KC.LL.HN.mm (emat GMf PARf LABf 729 i) (emat GMf PARf LABf 729 i))) = _
  rw [h2.2, h1.2, m, ← matJ_mul, ← matJ_mul]

theorem fld0 {x : ℕ} (hx : x < nPts) : fldW x (21 * 0) 21 = x := by
  unfold fldW
  change (x >>> 0) &&& (2 ^ 21 - 1) = x
  rw [Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt]
  change x < 1140000 at hx
  omega

theorem zero_mem_base : 0 ∈ Data.baseList := List.mem_cons_self

theorem cub_spec {i : ℕ} (hi : i < 729) :
    (memL SylowData.order3 i = true → Nat.beq (CFSG.KC.LL.HN.mm (EM i)
      (CFSG.KC.LL.HN.mm (EM i) (EM i))) CFSG.KD.OrdHN.ONE = true) ∧
    (memL SylowData.order3 i = false → i ≠ 0 →
      ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M
        (trM (CFSG.KC.LL.HN.mm (EM i) (CFSG.KC.LL.HN.mm (EM i) (EM i))))
        (g0 Data.baseList (fldW CK (Nat.mul 5 i) 5)) (f21 CY i) 1 = true ∧
      f21 CY i ≠ g0 Data.baseList (fldW CK (Nat.mul 5 i) 5)) := by
  have hc := cub_get hi
  unfold cub at hc
  generalize CFSG.KC.LL.HN.mm (EM i) (CFSG.KC.LL.HN.mm (EM i) (EM i)) = c at hc ⊢
  generalize g0 Data.baseList (fldW CK (Nat.mul 5 i) 5) = b at hc ⊢
  unfold cubF at hc
  rw [bi_eq] at hc
  refine ⟨fun hm => by rwa [if_pos hm] at hc, fun hm h0 => ?_⟩
  have hm' : ¬ (memL SylowData.order3 i = true) := fun e => by
    rw [hm] at e
    exact Bool.false_ne_true e
  rw [if_neg hm', bi_eq, if_neg (fun e => h0 (Nat.eq_of_beq_eq_true e)),
    ba_eq, Bool.and_eq_true] at hc
  refine ⟨hc.1, fun h => ?_⟩
  have := hc.2
  rw [h, Nat.beq_refl] at this
  exact Bool.false_ne_true this

theorem cube_one {i : ℕ} (hi : i < 729)
    (hm : SylowData.order3.contains i = true) : E i * (E i * E i) = 1 := by
  obtain ⟨cC, mC⟩ := cube_mat i
  have e := congrArg OM' (Nat.eq_of_beq_eq_true ((cub_spec hi).1 (by rw [memL_eq]; exact hm)))
  rw [mC, HNXP.one_ord, ← matJ_one] at e
  exact matJ_injective e

theorem g0_mem (k : ℕ) : g0 Data.baseList k ∈ Data.baseList := by
  by_cases hk : k < 22
  · unfold g0
    rw [List.getD_eq_getElem _ _ (by rw [base_len]; exact hk)]
    exact List.getElem_mem _
  · unfold g0
    rw [List.getD_eq_default _ _ (by rw [base_len]; omega)]
    exact zero_mem_base

theorem cube_move {i : ℕ} (hi : i < 729)
    (hm : SylowData.order3.contains i = false) (h0 : i ≠ 0) :
    ∃ b ∈ Data.baseList, gi (E i * (E i * E i)) b ≠ b := by
  obtain ⟨cC, mC⟩ := cube_mat i
  obtain ⟨hpt, hne⟩ := (cub_spec hi).2 (by rw [memL_eq]; exact hm) h0
  have hbm := g0_mem (fldW CK (Nat.mul 5 i) 5)
  obtain ⟨k, hk, hbk⟩ := base_mem hbm
  have hbl : g0 Data.baseList (fldW CK (Nat.mul 5 i) 5) < nPts := by rw [hbk]; exact base_lt hk
  have hy : f21 CY i < nPts := Nat.blt_eq.mp (allN_spec cy_lt i hi)
  have e := gi_pts cC mC (c := 1) (k := 0) (by norm_num) hpt (by norm_num)
    (by rw [fld0 hbl]; exact hbl) (by rw [fld0 hy]; exact hy)
  rw [fld0 hbl, fld0 hy] at e
  exact ⟨_, hbm, fun h => hne (e.symm.trans h)⟩

theorem mark_ok {i : ℕ} (hi : i < 729) :
    SylowData.order3.contains i = (i != 0 && Data.baseList.all fun b =>
      pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729 i
        (pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729 i
          (pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729 i b)) == b) := by
  have hp : ∀ b ∈ Data.baseList, pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val))
      FAData.pParents 729 i (pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729
        i (pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729 i b)) =
      gi (E i * (E i * E i)) b := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := base_mem hb
    have hb' := base_lt hk
    rw [pev_eq _ _ _ hb', pev_eq _ _ _ (gi_lt _ hb'), pev_eq _ _ _ (gi_lt _ (gi_lt _ hb')),
      gi_mul _ _ hb', gi_mul _ _ hb']
  by_cases hm : SylowData.order3.contains i = true
  · have e1 := cube_one hi hm
    have h0 : i ≠ 0 := fun h => by rw [h, order3_zero] at hm; exact absurd hm (by decide)
    rw [hm]
    symm
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, h0, not_false_eq_true, true_and,
      List.all_eq_true, beq_iff_eq]
    intro b hb
    rw [hp b hb, e1]
    obtain ⟨k, hk, rfl⟩ := base_mem hb
    exact gi_one (base_lt hk)
  · rw [Bool.eq_false_iff.mpr hm]
    by_cases h0 : i = 0
    · subst h0
      simp
    · obtain ⟨b, hbm, hne⟩ := cube_move hi (Bool.eq_false_iff.mpr hm) h0
      symm
      rw [Bool.eq_false_iff]
      intro h
      rw [Bool.and_eq_true, List.all_eq_true] at h
      have := h.2 b hbm
      rw [beq_iff_eq, hp b hbm] at this
      exact hne this

theorem pair_get0 (a b : Array ℕ) : (#[a, b] : Array (Array ℕ))[0]! = a := by
  rw [getElem!_pos _ 0 (by simp), List.getElem_toArray, List.getElem_cons_zero]

theorem pair_get1 (a b : Array ℕ) : (#[a, b] : Array (Array ℕ))[1]! = b := by
  rw [getElem!_pos _ 1 (by simp), List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero]

theorem ai0 : (pinvs nPts #[arrJ aJ, arrJ bJ])[0]! = arrJ aJ⁻¹ := by
  rw [pinvs_get (S := #[arrJ aJ, arrJ bJ]) (j := 0) (by simp), pair_get0, pinvCand_arrJ]

theorem ai1 : (pinvs nPts #[arrJ aJ, arrJ bJ])[1]! = arrJ bJ⁻¹ := by
  rw [pinvs_get (S := #[arrJ aJ, arrJ bJ]) (j := 1) (by simp), pair_get1, pinvCand_arrJ]

theorem rep_get {c : ℕ} (hc : c < 48) : rep c = true := by
  have h8 : c / 8 < 6 := by omega
  have := allN_spec (rK.all (c / 8) h8) (c % 8) (Nat.mod_lt _ (by norm_num))
  rwa [show Nat.add (Nat.mul 8 (c / 8)) (c % 8) = c from Nat.div_add_mod c 8] at this

theorem seedInv_gi : ∀ (w : List ℕ) {y : ℕ}, y < nPts →
    seedWordInvIdx (arrJ aJ⁻¹) (arrJ bJ⁻¹) w y = gi (seedJ w)⁻¹ y
  | [], _, hy => by rw [seedJ, inv_one, gi_one hy]; rfl
  | l :: w, y, hy => by
    have e1 : seedWordInvIdx (arrJ aJ⁻¹) (arrJ bJ⁻¹) (l :: w) y = seedWordInvIdx (arrJ aJ⁻¹)
        (arrJ bJ⁻¹) w ((if l = 1 then arrJ aJ⁻¹ else arrJ bJ⁻¹)[y]!) := rfl
    have e2 : (if l = 1 then arrJ aJ⁻¹ else arrJ bJ⁻¹)[y]! = gi (if l = 1 then aJ else bJ)⁻¹ y := by
      split_ifs <;> exact arrJ_get _ hy
    rw [e1, e2, seedInv_gi w (gi_lt _ hy), seedJ, _root_.mul_inv_rev, gi_mul _ _ hy]

theorem rep_ok {c : ℕ} (hc : c < 48) :
    (Data.baseList.all fun b => seedWordInvIdx (pinvs nPts #[arrJ aJ, arrJ bJ])[0]!
      (pinvs nPts #[arrJ aJ, arrJ bJ])[1]! FAData.wRoot[c]!
      (pev (Array.ofFn (n := 6) fun j => arrJ (PG j.val)) FAData.pParents 729 FAData.wRep[c]!
        (seedWordIdx (arrJ aJ) (arrJ bJ) FAData.wRoot[c]! b)) ==
      (pword nPts SJ (pinvs nPts SJ) FAData.wHWord[c]!)[b]!) = true := by
  obtain ⟨hr, hw, hh⟩ := rep_data c hc
  have h := rep_get hc
  unfold rep at h
  rw [sb_eq, sb_eq] at h
  obtain ⟨cS, mS⟩ := mat_word (cs := FAData.wRoot[c]!.map (33 + ·)) fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    rcases hw l hl with rfl | rfl <;> norm_num
  rw [prod_seed _ hw] at mS
  obtain ⟨cH, mH⟩ := strong_elem (w := FAData.wHWord[c]!) (cs := FAData.wHWord[c]!.map scodeK) rfl
    (by rw [scodeK_eq]) hh
  obtain ⟨cE, mE⟩ := EM_mat 729 FAData.wRep[c]!
  change Canon 5 133 13 (EM FAData.wRep[c]!) at cE
  change OM' (EM FAData.wRep[c]!) = _ at mE
  have e := congrArg OM' (Nat.eq_of_beq_eq_true h)
  rw [(HNXP.mm_sound cE cS).2, (HNXP.mm_sound cS cH).2, mE, mS, mH, ← matJ_mul, ← matJ_mul] at e
  have eg := matJ_injective e
  rw [ai0, ai1, List.all_eq_true]
  intro b hb
  obtain ⟨k, hk, rfl⟩ := base_mem hb
  have hb' := base_lt hk
  rw [beq_iff_eq, seedWordIdx_gi _ hb', pev_eq _ _ _ (gi_lt _ hb'), seedInv_gi _ (gi_lt _ (gi_lt _ hb')),
    pword_arrJ SJ_arrs _ hh, arrJ_get _ hb', ← gi_mul _ _ (gi_lt _ hb'), ← gi_mul _ _ hb']
  have eh : (seedJ FAData.wRoot[c]!)⁻¹ * EA 729 FAData.wRep[c]! * seedJ FAData.wRoot[c]! =
      wJ sL FAData.wHWord[c]! := by
    rw [mul_assoc, eg, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [eh]

theorem sylow_ok : sylowChecks (hnsData.orbit ()) = true := by
  have hreg := (progRegs_arrJ _ _ _ prog_lt (initRegs_get rfl rfl).1 (initRegs_get rfl rfl).2).1
  obtain ⟨t1, t2, t3, t4, t5, t6, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18⟩ :=
    tab_data
  have t7 : (FAData.pLift.all fun lw => lw.all fun l => decide (1 ≤ l) && decide (l ≤ 7)) = true := by
    rw [Array.all_eq_true]
    intro j hj
    rw [List.all_eq_true]
    intro l hl
    have hj5 : j < 5 := by rw [t6] at hj; exact hj
    have := lift_data.2.1 j hj5 l (by rw [getElem!_pos FAData.pLift j hj]; exact hl)
    simp [this.1, this.2]
  obtain ⟨p1, p2, p3⟩ := par_data
  unfold sylowChecks
  try dsimp only
  rw [hns_n, natTab_alpha, natTab_beta, hreg, regs_get (k := 1) (by omega),
    regs_get (k := 2) (by omega), hS_eq, c3_eq, G_eq, labels_eq,
    show (Array.ofFn (n := 729) fun i => SylowData.order3.contains i.val) = markL from rfl]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨trivial, strongOK_arrJ HNStrong.strong_parts.1 (by omega) words_lt,
    by rw [pinvs_size]; rfl, by rw [ai0]; exact pisInv_arrJ aJ, by rw [ai1]; exact pisInv_arrJ bJ,
    t1, CFSG.ONSchreier.allBelowN_iff.2 t2, t3, t4, t5, t6, t7, Array.size_ofFn, ?gp, p1, p2, ?pa,
    t8, ?lf, ?ds, t9, ?mk, t10, ?cj, t11, cls_size, ?w1, ?w2, t12, ?w3, t13, t14, t15, t16, t17, t18, ?w4⟩
  case pa =>
    refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
    by_cases h0 : i = 0
    · simp [h0]
    · have := p3 i hi h0
      simp [h0, this.1, this.2]
  case w1 =>
    simp only [allBelowN_eq]
    exact cls_a
  case w2 =>
    simp only [allBelowN_eq]
    exact cls_b
  case w3 =>
    simp only [allBelowN_eq]
    exact cls_c
  case gp =>
    exact CFSG.ONSchreier.allBelowN_iff.2 fun j hj => by
      rw [G_get hj, Gi_get hj]
      exact pisInv_arrJ _
  case lf =>
    refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rw [Bool.and_eq_true, beq_iff_eq]
    refine ⟨(left_data j hj).1, CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨(left_data j hj).2 i hi, left_ok hj hi⟩
  case ds =>
    refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => CFSG.ONSchreier.allBelowN_iff.2 fun k hk => ?_
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases h : k ≤ i
    · exact Or.inl h
    · exact Or.inr (bne_iff_ne.2 (dist_ok hi hk (by omega)))
  case mk =>
    refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
    rw [beq_iff_eq, markL, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    exact mark_ok hi
  case cj =>
    refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rw [Bool.and_eq_true, beq_iff_eq]
    refine ⟨(conj_data j hj).1, CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨(conj_data j hj).2 i hi, conj_ok hj hi⟩
  case w4 =>
    refine CFSG.ONSchreier.allBelowN_iff.2 fun c hc => ?_
    rw [rep_ok hc]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := wit_data c hc
    rw [show extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
      LocalData.strongWords = HNNat.natS from rfl, HNPt2108N.nat_w hc, HNPt2108N.nat_inv hc,
      HNPt2108N.nat_conj hc, a2, a3, a4]
    simp only [a1, a5, a6, decide_true, beq_self_eq_true, Bool.and_self]

end CertificateChecks.KernelSporSch.HNPt2108

end
