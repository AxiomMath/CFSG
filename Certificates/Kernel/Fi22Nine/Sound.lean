module

public import Certificates.Kernel.Fi22Nine.Cent
public import Certificates.Kernel.Fi22Nine.Let
public import Certificates.Kernel.Sporadic.Fi22.C2064
public import Certificates.Kernel.Sporadic.Fi22.E2065Eq
public import Certificates.Kernel.Sporadic.Fi22.F1Model
public import Certificates.Kernel.Sporadic.Fi22.HypWSound

public section

namespace CertificateChecks.KernelSpor.Fi22Nine

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CertificateChecks.KernelSpor
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Certificates.Native
open CertificateChecks.KernelSpor.Fi22F2 (gI bT)
open CFSG.Certificates (finSet)
open scoped Pointwise

theorem n9And {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true :=
  (bAnd_iff a b).1 h

theorem n9IfPos {c t e : Bool} (h : bIf(c, t, e) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

theorem n9IfNeg {c t e : Bool} (h : bIf(c, t, e) = true) (hc : c = false) : e = true := by
  subst hc
  exact h

theorem n9Not {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem n9Blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.blt_eq ▸ h

theorem n9TBlt {a b : Nat} (h : a < b) : Nat.blt a b = true := Nat.blt_eq ▸ h

theorem n9BeqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem n9SB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem n9SN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem n9All {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) : allN n f = true :=
  CFSG.KS.Raw.allN_of_forall h

theorem n9BT {t : Nat} (ht : t < 6) : bT t < 3510 := Fi22C3151.bT_lt ht

theorem cG_eq {j : Nat} (hj : j < 9) (y : Fin 3510) :
    cG j y = (fi22CentPerm (19 + j) y : Nat) := by
  have h := rep_fi22CentPerm (L := 19 + j) (by omega)
  rw [Fi22CtiA.cent_eq Fi22CentB.text_eq (by omega)] at h
  exact prep_of_rep h y

theorem cPerm_mem {j : Nat} (hj : j < 9) :
    fi22CentPerm (19 + j) ∈ fi22H 1 := by
  rw [fi22H_eq_closure (by norm_num)]
  exact Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem pG_eq {j : Nat} (hj : j < 2) (y : Fin 3510) :
    pG j y = (fi22GenPerm j y : Nat) := by
  have h := rep_fi22Gen hj
  rw [← fi22OrigArrs_get hj, Fi22F1M.orig_eq hj] at h
  exact prep_of_rep h y

theorem pPerm_mem {j : Nat} (hj : j < 2) : fi22GenPerm j ∈ fi22P := by
  rw [fi22P_eq]
  exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem tS_eq {s : Nat} (hs : s < 9) (y : Fin 3510) :
    tS s y = (fi22TSeed s y : Nat) := by
  have h := rep_fi22TSeed hs
  rw [Fi22X.outT_eq (by omega)] at h
  exact prep_of_rep h y

theorem tSeed_mem {s : Nat} (hs : s < 9) : fi22TSeed s ∈ fi22OuterT := by
  rw [fi22OuterT_eq_closure]
  exact Subgroup.subset_closure ⟨s, hs, rfl⟩

theorem zO_eq (y : Fin 3510) : zO y = (fi22ExtRep 1 y : Nat) :=
  Fi22CB.prep_ext (k := 1) (by norm_num) y

theorem uO_eq (y : Fin 3510) : uO y = (fi22U y : Nat) :=
  Fi22W.prep_GO y

theorem gI_eq {I : Nat} (hI : I < 131072) (y : Fin 3510) :
    gI I y = (fi22TProd (Fi22C3151.xF I) y : Nat) :=
  Fi22C3151.gI_eq hI y

@[expose] noncomputable def wP (G : Nat → Equiv.Perm (Fin 3510)) (i : Nat) :
    Nat → Equiv.Perm (Fin 3510)
  | 0 => 1
  | n + 1 => wP G i n * G (wL i n)

theorem walk_succ (G : Nat → Nat → Nat) (i n y : Nat) :
    walk G i (n + 1) y = walk G i n (G (wL i n) y) :=
  n9SN (G (wL i n) y) (fun y => walk G i n y)

theorem walk_eq {Gn : Nat → Nat → Nat} {G : Nat → Equiv.Perm (Fin 3510)} {B i : Nat}
    (hG : ∀ j < B, ∀ y : Fin 3510, Gn j y = (G j y : Nat)) :
    ∀ n, (∀ k < n, wL i k < B) → ∀ y : Fin 3510, walk Gn i n y = (wP G i n y : Nat)
  | 0, _, _ => rfl
  | n + 1, hl, y => by
    rw [walk_succ, hG _ (hl n (by omega)) y, walk_eq hG n (fun k hk => hl k (by omega)), wP,
      Equiv.Perm.mul_apply]

theorem wP_mem {G : Nat → Equiv.Perm (Fin 3510)} {B i : Nat} {H : Subgroup (Equiv.Perm (Fin 3510))}
    (hG : ∀ j < B, G j ∈ H) : ∀ n, (∀ k < n, wL i k < B) → wP G i n ∈ H
  | 0, _ => H.one_mem
  | n + 1, hl => H.mul_mem (wP_mem hG n fun k hk => hl k (by omega)) (hG _ (hl n (by omega)))

theorem letB_spec {i n B : Nat} (h : letB i n B = true) : ∀ k < n, wL i k < B :=
  fun k hk => n9Blt (allN_spec h k hk)

theorem sepB
    {X Y : Equiv.Perm (Fin 3510)} (hX : X ∈ fi22P) (hY : Y ∈ fi22P)
    (h : ∀ t (ht : t < 6), (X ⟨bT t, n9BT ht⟩ : Nat) = Y ⟨bT t, n9BT ht⟩) : X = Y := by
  have e : Y⁻¹ * X = 1 := by
    refine Fi22C3150.sepP (fi22P.mul_mem (fi22P.inv_mem hY) hX) fun r hr hrl => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h 0 (by norm_num)
    · exact h 1 (by norm_num)
    · exact h 2 (by norm_num)
    · exact h 3 (by norm_num)
    · exact h 5 (by norm_num)
    · exact h 4 (by norm_num)
  exact (inv_mul_eq_one.mp e).symm

theorem eqB_eq
    {f f' : Nat → Nat} {X Y : Equiv.Perm (Fin 3510)}
    (hf : ∀ y : Fin 3510, f y = (X y : Nat)) (hf' : ∀ y : Fin 3510, f' y = (Y y : Nat))
    (hX : X ∈ fi22P) (hY : Y ∈ fi22P) (h : eqB f f' = true) : X = Y :=
  sepB hX hY fun t ht =>
    (hf ⟨bT t, n9BT ht⟩).symm.trans
      ((Nat.eq_of_beq_eq_true (allN_spec h t ht)).trans (hf' ⟨bT t, n9BT ht⟩))

theorem eqB_of_eq {f f' : Nat → Nat} {X Y : Equiv.Perm (Fin 3510)}
    (hf : ∀ y : Fin 3510, f y = (X y : Nat)) (hf' : ∀ y : Fin 3510, f' y = (Y y : Nat))
    (h : X = Y) : eqB f f' = true :=
  n9All fun t ht => by
    have e1 : f (bT t) = (X ⟨bT t, n9BT ht⟩ : Nat) := hf ⟨bT t, n9BT ht⟩
    have e2 : f' (bT t) = (Y ⟨bT t, n9BT ht⟩ : Nat) := hf' ⟨bT t, n9BT ht⟩
    rw [e1, e2, h]
    exact Nat.beq_refl _

theorem ne_of_eqB {f f' : Nat → Nat} {X Y : Equiv.Perm (Fin 3510)}
    (hf : ∀ y : Fin 3510, f y = (X y : Nat)) (hf' : ∀ y : Fin 3510, f' y = (Y y : Nat))
    (h : Bool.not (eqB f f') = true) : X ≠ Y := fun e => by
  rw [eqB_of_eq hf hf' e] at h
  exact absurd h (by decide)

theorem memL_iff (l : List Nat) (y : Nat) : memL l y = true ↔ y ∈ l := by
  induction l with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h List.not_mem_nil⟩
  | cons a l ih =>
    change bIf(Nat.beq a y, true, memL l y) = true ↔ y ∈ a :: l
    rw [List.mem_cons, ← ih]
    cases e : Nat.beq a y
    · have hne : y ≠ a := fun h => by rw [h, Nat.beq_refl] at e; exact Bool.noConfusion e
      exact ⟨Or.inr, fun h => h.resolve_left hne⟩
    · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true e).symm, fun _ => rfl⟩

theorem smul_finSet_eq {l : List Nat} {m : Nat} {f : Nat → Nat} {σ : Equiv.Perm (Fin 3510)}
    (hm : l.length = m) (hσ : ∀ y : Fin 3510, f y = (σ y : Nat)) (h : fixL l m f = true) :
    σ • finSet 3510 l = finSet 3510 l := by
  have hsub : σ • finSet 3510 l ⊆ finSet 3510 l := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : Nat) ∈ l := hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hx'
    have hg : l.getD i 0 = x := by rw [List.getD_eq_getElem _ _ hi, hix]
    have hmem := allN_spec h i (hm ▸ hi)
    rw [hg, memL_iff, hσ x] at hmem
    exact hmem
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) (Set.toFinite _)

section Orbit

variable {o m n : Nat} {X : List Nat}

theorem row_parts {k : Nat} (h : rowO o m n X k = true) :
    (∀ i < m - 1, oP o m k i < oP o m k (i + 1)) ∧ oP o m k (m - 1) < 3510 ∧
    (k + 1 < n → keyO o m k < keyO o m (k + 1)) ∧
    (k = oF o 5 0 → (∀ i < m, oP o m k i = X.getD i 0) ∧
      ∀ s < 9, mapsO o m k k (tS s) = true) ∧
    (k ≠ oF o 5 0 → oF o 1 k < n ∧ oF o 3 (oF o 1 k) < oF o 3 k ∧ oF o 2 k < 9 ∧
      mapsO o m (oF o 1 k) k (cG (oF o 2 k)) = true ∧ oF o 4 k < 9 ∧
      mapsO o m k k (tS (oF o 4 k)) = false) := by
  unfold rowO at h
  obtain ⟨hA, h⟩ := n9And h
  obtain ⟨hB, h⟩ := n9And h
  obtain ⟨hC, hD⟩ := n9And h
  refine ⟨fun i hi => n9Blt (allN_spec hA i hi), n9Blt hB, fun hk => ?_, fun hk => ?_,
    fun hk => ?_⟩
  · exact n9Blt (n9IfPos hC (n9TBlt hk))
  · have hE := n9IfPos hD (by rw [hk]; exact Nat.beq_refl _)
    obtain ⟨h1, h2⟩ := n9And hE
    obtain ⟨-, h3⟩ := n9And h2
    exact ⟨fun i hi => Nat.eq_of_beq_eq_true (allN_spec h1 i hi), fun s hs => allN_spec h3 s hs⟩
  · have hF := n9IfNeg hD (n9BeqF hk)
    simp only [n9SB] at hF
    obtain ⟨h1, hF⟩ := n9And hF
    obtain ⟨h2, hF⟩ := n9And hF
    obtain ⟨h3, hF⟩ := n9And hF
    obtain ⟨h4, hF⟩ := n9And hF
    obtain ⟨h5, h6⟩ := n9And hF
    exact ⟨n9Blt h1, n9Blt h2, n9Blt h3, h4, n9Blt h5, n9Not h6⟩

theorem memO_iff {k y : Nat} : memO o m k y = true ↔ ∃ i < m, oP o m k i = y := by
  unfold memO
  constructor
  · intro h
    by_contra hc
    have hall : allN m (fun i => Bool.not (Nat.beq (oP o m k i) y)) = true :=
      n9All fun i hi => by rw [n9BeqF fun e => hc ⟨i, hi, e⟩]; rfl
    rw [hall] at h
    exact absurd h (by decide)
  · rintro ⟨i, hi, rfl⟩
    cases e : allN m (fun i' => Bool.not (Nat.beq (oP o m k i') (oP o m k i)))
    · rfl
    · have h := allN_spec e i hi
      rw [Nat.beq_refl] at h
      exact absurd h (by decide)

theorem pts_facts {k : Nat} (hm : 0 < m) (h : rowO o m n X k = true) :
    (∀ i < m, oP o m k i < 3510) ∧ ∀ i j, i < j → j < m → oP o m k i < oP o m k j := by
  obtain ⟨hinc, hlast, -⟩ := row_parts h
  have hmono : ∀ i j, i < j → j < m → oP o m k i < oP o m k j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := hinc j (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | rfl
      · exact (ih hlt (by omega)).trans hs
      · exact hs
  refine ⟨fun i hi => ?_, hmono⟩
  rcases Nat.lt_or_ge i (m - 1) with hlt | hge
  · exact (hmono i (m - 1) hlt (by omega)).trans hlast
  · have : i = m - 1 := by omega
    rw [this]
    exact hlast

@[expose] noncomputable def trF (o m k : Nat) : Finset (Fin 3510) :=
  Finset.univ.image fun i : Fin m => (⟨oP o m k i % 3510, Nat.mod_lt _ (by norm_num)⟩ : Fin 3510)

theorem mem_trF {k : Nat} (hm : 0 < m) (h : rowO o m n X k = true) (p : Fin 3510) :
    p ∈ trF o m k ↔ ∃ i < m, oP o m k i = p := by
  have hlt := (pts_facts hm h).1
  unfold trF
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, i.2, by simp [Nat.mod_eq_of_lt (hlt i i.2)]⟩
  · rintro ⟨i, hi, e⟩
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, Fin.ext (by simp [Nat.mod_eq_of_lt (hlt i hi), e])⟩

theorem card_trF {k : Nat} (hm : 0 < m) (h : rowO o m n X k = true) : (trF o m k).card = m := by
  obtain ⟨hlt, hmono⟩ := pts_facts hm h
  unfold trF
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j e
  have e' : oP o m k i = oP o m k j := by
    have := congrArg Fin.val e
    simpa [Nat.mod_eq_of_lt (hlt i i.2), Nat.mod_eq_of_lt (hlt j j.2)] using this
  rcases lt_trichotomy (i : Nat) j with hij | hij | hij
  · exact absurd e' (hmono i j hij j.2).ne
  · exact Fin.ext hij
  · exact absurd e' (hmono j i hij i.2).ne'

theorem coe_image_perm (s : Finset (Fin 3510)) (σ : Equiv.Perm (Fin 3510)) :
    ((s.image σ : Finset (Fin 3510)) : Set (Fin 3510)) = σ • (s : Set (Fin 3510)) := by
  rw [Finset.coe_image]
  rfl

theorem image_trF {j k : Nat} {f : Nat → Nat} {σ : Equiv.Perm (Fin 3510)} (hm : 0 < m)
    (hj : rowO o m n X j = true) (hk : rowO o m n X k = true)
    (hσ : ∀ y : Fin 3510, f y = (σ y : Nat)) (h : mapsO o m j k f = true) :
    (trF o m j).image σ = trF o m k := by
  have hsub : (trF o m j).image σ ⊆ trF o m k := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨i, hi, e0⟩ := (mem_trF hm hj q).1 hq
    have hmem : memO o m k (f (oP o m j i)) = true := allN_spec h i hi
    rw [e0, memO_iff] at hmem
    obtain ⟨i', hi', e⟩ := hmem
    exact (mem_trF hm hk _).2 ⟨i', hi', e.trans (hσ q)⟩
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_of_injective _ σ.injective, card_trF hm hj, card_trF hm hk]

theorem mapsO_of_fix {k : Nat} {f : Nat → Nat} {σ : Equiv.Perm (Fin 3510)} (hm : 0 < m)
    (hk : rowO o m n X k = true) (hσ : ∀ y : Fin 3510, f y = (σ y : Nat))
    (h : σ • (trF o m k : Set (Fin 3510)) = trF o m k) : mapsO o m k k f = true := by
  have hlt := (pts_facts hm hk).1
  refine n9All fun i hi => ?_
  rw [memO_iff]
  have hq : (⟨oP o m k i, hlt i hi⟩ : Fin 3510) ∈ trF o m k := (mem_trF hm hk _).2 ⟨i, hi, rfl⟩
  have hσq : σ ⟨oP o m k i, hlt i hi⟩ ∈ (trF o m k : Set (Fin 3510)) := by
    rw [← h]
    exact Set.smul_mem_smul_set hq
  obtain ⟨i', hi', e⟩ := (mem_trF hm hk _).1 hσq
  exact ⟨i', hi', e.trans (hσ _).symm⟩

theorem pts_eq_of_trF_eq {j k : Nat} (hm : 0 < m) (hj : rowO o m n X j = true)
    (hk : rowO o m n X k = true) (h : trF o m j = trF o m k) :
    ∀ p, (∃ i < m, oP o m j i = p) ↔ ∃ i < m, oP o m k i = p := by
  obtain ⟨hltj, -⟩ := pts_facts hm hj
  obtain ⟨hltk, -⟩ := pts_facts hm hk
  intro p
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hp : (⟨oP o m j a, hltj a ha⟩ : Fin 3510) ∈ trF o m k := by
      rw [← h]
      exact (mem_trF hm hj _).2 ⟨a, ha, rfl⟩
    exact (mem_trF hm hk _).1 hp
  · rintro ⟨a, ha, rfl⟩
    have hp : (⟨oP o m k a, hltk a ha⟩ : Fin 3510) ∈ trF o m j := by
      rw [h]
      exact (mem_trF hm hk _).2 ⟨a, ha, rfl⟩
    exact (mem_trF hm hj _).1 hp

theorem testBit_key (k p : Nat) : ∀ m', (Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (oP o m k i))) m').testBit p = true ↔
      ∃ i < m', oP o m k i = p
  | 0 => by simp
  | m' + 1 => by
    change ((Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (oP o m k i))) m') |||
      (1 <<< (oP o m k m'))).testBit p = true ↔ _
    rw [Nat.testBit_lor, Bool.or_eq_true, testBit_key k p m', Nat.shiftLeft_eq, one_mul,
      Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, e⟩ | e)
      · exact ⟨i, by omega, e⟩
      · exact ⟨m', by omega, e⟩
    · rintro ⟨i, hi, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact Or.inl ⟨i, h, e⟩
      · exact Or.inr e

theorem keyO_congr {j k : Nat} (h : ∀ p, (∃ i < m, oP o m j i = p) ↔ ∃ i < m, oP o m k i = p) :
    keyO o m j = keyO o m k :=
  Nat.eq_of_testBit_eq fun p => by
    rw [Bool.eq_iff_iff]
    unfold keyO
    rw [testBit_key, testBit_key]
    exact h p

theorem keyO_lt (hrow : ∀ k < n, rowO o m n X k = true) {j k : Nat} (hjk : j < k) (hk : k < n) :
    keyO o m j < keyO o m k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hs := (row_parts (hrow k (by omega))).2.2.1 hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hlt | rfl
    · exact (ih hlt (by omega)).trans hs
    · exact hs

theorem trF_inj (hm : 0 < m) (hrow : ∀ k < n, rowO o m n X k = true) {j k : Nat} (hj : j < n)
    (hk : k < n) (h : trF o m j = trF o m k) : j = k := by
  have hkey := keyO_congr (pts_eq_of_trF_eq hm (hrow j hj) (hrow k hk) h)
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · exact absurd hkey (keyO_lt hrow hjk hk).ne
  · exact hjk
  · exact absurd hkey (keyO_lt hrow hjk hj).ne'

theorem trF_start (hm : 0 < m) (hX : X.length = m) (hrow : ∀ k < n, rowO o m n X k = true)
    (hs : oF o 5 0 < n) : (trF o m (oF o 5 0) : Set (Fin 3510)) = finSet 3510 X := by
  have hrs := hrow _ hs
  have hpts := ((row_parts hrs).2.2.2.1 rfl).1
  ext p
  rw [Finset.mem_coe, mem_trF hm hrs]
  change _ ↔ (p : Nat) ∈ X
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, e⟩
    refine ⟨i, hX ▸ hi, ?_⟩
    rw [← e, hpts i hi, List.getD_eq_getElem _ _ (hX ▸ hi)]
  · rintro ⟨i, hi, e⟩
    refine ⟨i, hX ▸ hi, ?_⟩
    rw [hpts i (hX ▸ hi), List.getD_eq_getElem _ _ hi, e]

theorem trF_mem (hm : 0 < m) (hX : X.length = m)
    (hrow : ∀ k < n, rowO o m n X k = true) (hs : oF o 5 0 < n) :
    ∀ k < n, ∃ c ∈ fi22H 1, (trF o m k : Set (Fin 3510)) = c • finSet 3510 X := by
  have key : ∀ d k, k < n → oF o 3 k ≤ d →
      ∃ c ∈ fi22H 1, (trF o m k : Set (Fin 3510)) = c • finSet 3510 X := by
    intro d
    induction d with
    | zero =>
      intro k hk hd
      by_cases hks : k = oF o 5 0
      · subst hks
        exact ⟨1, (fi22H 1).one_mem, by rw [one_smul, trF_start hm hX hrow hs]⟩
      · have := ((row_parts (hrow k hk)).2.2.2.2 hks).2.1
        omega
    | succ d ih =>
      intro k hk hd
      by_cases hks : k = oF o 5 0
      · subst hks
        exact ⟨1, (fi22H 1).one_mem, by rw [one_smul, trF_start hm hX hrow hs]⟩
      · obtain ⟨hj, hdep, hsg, hmap, -⟩ := (row_parts (hrow k hk)).2.2.2.2 hks
        obtain ⟨c, hc, e⟩ := ih _ hj (by omega)
        have himg := image_trF hm (hrow _ hj) (hrow k hk) (cG_eq hsg) hmap
        refine ⟨fi22CentPerm (19 + oF o 2 k) * c, (fi22H 1).mul_mem (cPerm_mem hsg) hc, ?_⟩
        rw [← himg, coe_image_perm, e, mul_smul]
  exact fun k hk => key _ k hk le_rfl

theorem orb_lower (hm : 0 < m) (hX : X.length = m)
    (hrow : ∀ k < n, rowO o m n X k = true) (hs : oF o 5 0 < n) :
    n ≤ (Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X).ncard := by
  classical
  let F : Fin n → Set (Fin 3510) := fun k => (trF o m k : Set (Fin 3510))
  have hinj : Function.Injective F := fun i j e =>
    Fin.ext (trF_inj hm hrow i.2 j.2 (Finset.coe_injective e))
  have hsub : Set.range F ⊆ Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hc, e⟩ := trF_mem hm hX hrow hs k k.2
    exact ⟨⟨c, hc⟩, e.symm⟩
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_range_of_injective hinj, Nat.card_fin] at h

theorem orb_unique (hm : 0 < m)
    (hX : X.length = m) (hrow : ∀ k < n, rowO o m n X k = true) (hs : oF o 5 0 < n)
    (horb : (Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X).ncard = n) :
    ∀ y ∈ Set.range (fun g : ↥(fi22H 1) => g • finSet 3510 X),
      (∀ t ∈ fi22OuterT, t • y = y) → y = finSet 3510 X := by
  classical
  let F : Fin n → Set (Fin 3510) := fun k => (trF o m k : Set (Fin 3510))
  have hinj : Function.Injective F := fun i j e =>
    Fin.ext (trF_inj hm hrow i.2 j.2 (Finset.coe_injective e))
  have hsub : Set.range F ⊆ Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hc, e⟩ := trF_mem hm hX hrow hs k k.2
    exact ⟨⟨c, hc⟩, e.symm⟩
  have hEq : Set.range F = Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X :=
    Set.eq_of_subset_of_ncard_le hsub
      (by rw [horb, Set.ncard_range_of_injective hinj, Nat.card_fin]) (Set.toFinite _)
  intro y hy hfix
  rw [← hEq] at hy
  obtain ⟨k, rfl⟩ := hy
  by_cases hks : (k : Nat) = oF o 5 0
  · change (trF o m k : Set (Fin 3510)) = _
    rw [hks]
    exact trF_start hm hX hrow hs
  · obtain ⟨-, -, -, -, hw, hnot⟩ := (row_parts (hrow k k.2)).2.2.2.2 hks
    have hm' := mapsO_of_fix hm (hrow k k.2) (tS_eq hw) (hfix _ (tSeed_mem hw))
    rw [hnot] at hm'
    exact absurd hm' (by decide)

end Orbit

theorem tProd_eq_gI (x : Fin 1024 × Fin 32 × Fin 4) (y : Fin 3510) :
    gI (Fi22C3151.iX x) y = (fi22TProd x y : Nat) := by
  rw [gI_eq (Fi22C3151.iX_lt x), Fi22C3151.xF_iX]

theorem centK_of {I : Nat} (hI : I < 131072) : centK I = true := by
  have hq : I / 4096 < 32 := by omega
  have h := centAll (I / 4096) hq
  unfold centSl at h
  have e : Nat.add (Nat.mul (I / 4096) 4096) (I % 4096) = I := by
    change I / 4096 * 4096 + I % 4096 = I
    omega
  have := allN_spec h (I % 4096) (Nat.mod_lt _ (by norm_num))
  rw [e] at this
  exact this

set_option maxRecDepth 100000 in
theorem center_eq
    {t : Equiv.Perm (Fin 3510)} (ht : t ∈ fi22OuterT)
    (hc : ∀ y ∈ fi22OuterT, t * y = y * t) (hz : fi22ExtRep 1 ∈ fi22P) :
    t = 1 ∨ t = fi22ExtRep 1 := by
  obtain ⟨x, rfl⟩ := fi22TProd_surj ht
  have hgI := tProd_eq_gI x
  have hK := centK_of (Fi22C3151.iX_lt x)
  have hB : centB (Fi22C3151.iX x) = true := by
    unfold centB
    refine n9All fun s hs => n9All fun u hu => ?_
    have e := congrArg (fun g : Equiv.Perm (Fin 3510) => (g ⟨bT u, n9BT hu⟩ : Nat))
      (hc _ (tSeed_mem hs))
    simp only [Equiv.Perm.mul_apply] at e
    unfold commB
    have e1 : tS s (bT u) = (fi22TSeed s ⟨bT u, n9BT hu⟩ : Nat) :=
      tS_eq hs ⟨bT u, n9BT hu⟩
    have e2 : gI (Fi22C3151.iX x) (bT u) = (fi22TProd x ⟨bT u, n9BT hu⟩ : Nat) :=
      hgI ⟨bT u, n9BT hu⟩
    rw [e1, hgI, e2, tS_eq hs, e]
    exact Nat.beq_refl _
  have hK' : bIf(centB (Fi22C3151.iX x), oneOrZ zP (Fi22C3151.iX x), true) = true := hK
  have hO : bIf(allN 6 fun u => Nat.beq (gI (Fi22C3151.iX x) (bT u)) (bT u), true,
      allN 6 fun u => Nat.beq (gI (Fi22C3151.iX x) (bT u)) (zO (bT u))) = true :=
    n9IfPos hK' hB
  have hP : fi22TProd x ∈ fi22P := fi22OuterT_le (fi22TProd_mem x)
  cases e : allN 6 fun u => Nat.beq (gI (Fi22C3151.iX x) (bT u)) (bT u)
  · have h2 := n9IfNeg hO e
    right
    refine sepB hP hz fun u hu => ?_
    have h3 := Nat.eq_of_beq_eq_true (allN_spec h2 u hu)
    have e2 : gI (Fi22C3151.iX x) (bT u) = (fi22TProd x ⟨bT u, n9BT hu⟩ : Nat) :=
      hgI ⟨bT u, n9BT hu⟩
    have e3 : zO (bT u) = (fi22ExtRep 1 ⟨bT u, n9BT hu⟩ : Nat) :=
      zO_eq ⟨bT u, n9BT hu⟩
    rw [e2, e3] at h3
    exact h3
  · left
    refine sepB hP fi22P.one_mem fun u hu => ?_
    have h3 := Nat.eq_of_beq_eq_true (allN_spec e u hu)
    have e2 : gI (Fi22C3151.iX x) (bT u) = (fi22TProd x ⟨bT u, n9BT hu⟩ : Nat) :=
      hgI ⟨bT u, n9BT hu⟩
    rw [e2] at h3
    exact h3

end CertificateChecks.KernelSpor.Fi22Nine

end
