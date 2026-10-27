module

public import CFSG.Quasithin.Recognition.St84.G24DecompFacts
public import Certificates.Kernel.G24B.Normal
public import Certificates.Kernel.G24B.Checks733007
import CFSG.GroupTheory.ClosurePairCommute

public section

noncomputable section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.Fischer CFSG.Quasithin.F112R.St84.G24M CFSG.KC.Misc.Spec CFSG.KC.F2BfsRec
open CFSG.KC.Misc.G24 (mulF2 oneF2 wordF4 nthV nthL nthLL)
open CFSG.Quasithin.St84.G24Ident (k1 k2 xa xb)
open CFSG.Quasithin.F112R.St84

theorem orB_iff' {a b : Bool} : CFSG.KLie.CT.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [CFSG.KLie.CT.orB]

theorem bIf_true' {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem bIf_false' {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = false) : e = true := by
  subst hc
  exact h

theorem dcZipK_spec {α : Type} {d : α} {f : ℕ → α → Bool} :
    ∀ {L : List ℕ} {D : List α}, dcZipK d f L D = true → ∀ i < L.length, f (L.getD i 0) (D.getD i d) = true
  | [], _, _ => by simp
  | x :: L, [], h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro i hi
    rcases i with _ | i
    · exact h1
    · have := dcZipK_spec (L := L) (D := []) h2 i (by simpa using hi)
      simpa using this
  | x :: L, y :: D, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro i hi
    rcases i with _ | i
    · exact h1
    · have := dcZipK_spec (L := L) (D := D) h2 i (by simpa using hi)
      simpa using this

theorem testBit_of_dcBit {M x : ℕ} (h : dcBit M x = true) : M.testBit x = true := by
  have h' : 0 < M &&& 2 ^ x := by
    have := Nat.le_of_ble_eq_true h
    have e : M &&& 2 ^ x = Nat.land M (Nat.shiftLeft 1 x) := by
      rw [← Nat.one_shiftLeft]
      rfl
    rw [e]
    exact this
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.mp h')
  rw [Nat.testBit_and, Bool.and_eq_true, Nat.testBit_two_pow] at hi
  obtain ⟨h1, h2⟩ := hi
  rw [decide_eq_true_eq] at h2
  subst h2
  exact h1

theorem mem_of_testBit_dcMaskOf {x : ℕ} : ∀ {L : List ℕ}, (dcMaskOf L).testBit x = true → x ∈ L
  | [], h => by
    change Nat.testBit 0 x = true at h
    simp at h
  | y :: L, h => by
    change (Nat.lor (Nat.shiftLeft 1 y) (dcMaskOf L)).testBit x = true at h
    change ((1 <<< y) ||| dcMaskOf L).testBit x = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · subst h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_testBit_dcMaskOf h)

@[expose] def ltrM {M : Type*} [Monoid M] (z : Fin 4 → M) (c : ℕ) : M :=
  if h : c / 2 < 4 then (if c % 2 = 1 then z ⟨c / 2, h⟩ * z ⟨c / 2, h⟩ else z ⟨c / 2, h⟩) else 1

@[expose] def evM {M : Type*} [Monoid M] (z : Fin 4 → M) (w : List ℕ) : M := (w.map (ltrM z)).prod

theorem map_evM {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (z : Fin 4 → M) (w : List ℕ) :
    f (evM z w) = evM (fun k => f (z k)) w := by
  induction w with
  | nil => simp [evM]
  | cons c w ih =>
    simp only [evM, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    unfold ltrM
    split_ifs <;> simp [map_mul]

theorem dcLet_eq (im : List ℕ) (c : ℕ) :
    dcLet im c = if c % 2 = 1 then mulF2 28 (nthV im (c / 2)) (nthV im (c / 2)) else nthV im (c / 2) := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · have h' : Nat.mod c 2 = 0 := h
    rw [if_neg (by omega)]
    unfold dcLet
    rw [h']
    rfl
  · have h' : Nat.mod c 2 = 1 := h
    rw [if_pos h]
    unfold dcLet
    rw [h']
    rfl

theorem pk_dcEvS (hC : ChevFacts) {im : List ℕ} {z : Fin 4 → Y}
    (hz : ∀ k : Fin 4, psi (z k) = pkMat 28 (nthV im k.val)) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 8) → psi (evM z w) = pkMat 28 (dcEvS im w)
  | [], _ => by
    change psi (List.prod []) = pkMat 28 (oneF2 28)
    rw [List.prod_nil, map_one, pkMat_oneF2]
  | c :: w, hw => by
    have hc : c / 2 < 4 := by have := hw c (by simp); omega
    change psi (ltrM z c * evM z w) = pkMat 28 (mulF2 28 (dcLet im c) (dcEvS im w))
    rw [map_mul, pkMat_mulF2, pk_dcEvS hC hz w (fun c' hc' => hw c' (by simp [hc'])), dcLet_eq]
    unfold ltrM
    rw [dif_pos hc]
    have e := hz ⟨c / 2, hc⟩
    split_ifs
    · rw [map_mul, e, pkMat_mulF2]
    · rw [e]

theorem dcEvS_lt (im w : List ℕ) : dcEvS im w < 2 ^ (28 * 28) := by
  cases w with
  | nil => exact oneF2_lt
  | cons c w => exact mulF2_lt' _ _

theorem psi_pow_dcPow {y : Y} {X : ℕ} (hy : psi y = pkMat 28 X) :
    ∀ e : ℕ, psi (y ^ e) = pkMat 28 (dcPow X e)
  | 0 => by rw [pow_zero, map_one]; exact (pkMat_oneF2 28).symm
  | e + 1 => by
    change psi (y ^ (e + 1)) = pkMat 28 (mulF2 28 (dcPow X e) X)
    rw [pow_succ, map_mul, pkMat_mulF2, psi_pow_dcPow hy e, hy]

theorem dcX_eq {c s : ℕ} (hs : s < 1024) :
    dcX (1024 * c + s) = mulF2 28 (sortedAt 28 12 6 10 EQ2.CF s) (repK rw (nthV dcI4 c)) := by
  have h1 : Nat.mod (1024 * c + s) 1024 = s := by
    change (1024 * c + s) % 1024 = s
    omega
  have h2 : Nat.div (1024 * c + s) 1024 = c := by
    change (1024 * c + s) / 1024 = c
    omega
  unfold dcX
  rw [h1, h2]

theorem rY_mem_B0 (hM : Facts) (i : ℕ) : rY i ∈ B0 := by
  rw [← hM.closure_gB0]
  refine yW_mem (fun g hg => ?_) _
  simp only [gsB, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩
  · exact Subgroup.subset_closure ⟨3, rfl⟩

theorem exists_pos_of_sq (hC : ChevFacts) (hM : Facts) {y : Y} (hy : y ∈ B0) (h2 : y * y = 1) :
    ∃ x < 4096, psi y = pkMat 28 (dcX x) := by
  have hy' : y ∈ Subgroup.closure (Set.range gB0) := by rw [hM.closure_gB0]; exact hy
  obtain ⟨i, hi, q, hq, rfl⟩ := inCos_of_mem hC hy'
  have hNQ : B0 ≤ Subgroup.normalizer (Q2 : Set Y) := hM.B0_le_M2.trans hM.M2_le_normalizer_Q2
  have hrr : rY i * rY i ∈ Q2 := by
    have hc : rY i * q * (rY i)⁻¹ ∈ Q2 := mem_Q2_normal hNQ (rY_mem_B0 hM i) hq
    have e : rY i * rY i = (rY i * q * (rY i)⁻¹)⁻¹ * q⁻¹ * (q * rY i * (q * rY i)) := by group
    rw [e, h2, mul_one]
    exact Q2.mul_mem (Q2.inv_mem hc) (Q2.inv_mem hq)
  have hcos := ch733007_cos
  unfold dcCosK at hcos
  obtain ⟨hc4, hcos⟩ := andB_iff.mp hcos
  have e := allN_iff'.mp hcos i hi
  cases hin : dcIn4 i with
  | false =>
    have e2 := bIf_false' e hin
    rw [strictB_eq'] at e2
    exact absurd hrr (not_mem_of_gap (rQ2 hC) (mulF2_lt' _ _)
      (by rw [map_mul, psi_rY hC hi, ← pkMat_mulF2]) e2)
  | true =>
    have hc : ∃ c < 4, i = nthV dcI4 c := by
      unfold dcIn4 at hin
      rcases orB_iff'.mp hin with h | h
      · exact ⟨0, by norm_num, beq_iff'.mp h⟩
      rcases orB_iff'.mp h with h | h
      · exact ⟨1, by norm_num, beq_iff'.mp h⟩
      rcases orB_iff'.mp h with h | h
      · exact ⟨2, by norm_num, beq_iff'.mp h⟩
      · exact ⟨3, by norm_num, beq_iff'.mp h⟩
    obtain ⟨c, hc, rfl⟩ := hc
    obtain ⟨t, ht, he⟩ := exists_entry_of_recOK (rQ2 hC) hq
    obtain ⟨s, hs, hse⟩ := exists_sorted_of_entry (rQ2 hC).h ht
    refine ⟨1024 * c + s, by omega, ?_⟩
    rw [dcX_eq hs, map_mul, he, psi_rY hC hi, ← hse, ← pkMat_mulF2]

theorem ord2K_of {X : ℕ} (h1 : mulF2 28 X X = oneF2 28) (h2 : X ≠ oneF2 28) : ord2K X = true := by
  unfold ord2K
  rw [h1, Nat.beq_refl]
  cases hb : Nat.beq X (oneF2 28) with
  | false => rfl
  | true => exact absurd (beq_iff'.mp hb) h2

theorem dcScan_spec {cm : List ℕ} {lo n : ℕ} (h : dcScanK cm lo n = true) :
    ∀ i < n, Bool.rec (motive := fun _ => Bool) true
      (CFSG.KLie.CT.allN 8 fun a => Bool.rec (motive := fun _ => Bool) true
        (dcBit (nthV cm a) (lo + i)) (commK (dcX (lo + i)) (nthV dcHm (Nat.succ a))))
      (ord2K (dcX (lo + i))) = true := by
  intro i hi
  have e := allN_iff'.mp h i hi
  rw [strictB_eq'] at e
  exact e

theorem mem_cl {x : ℕ} (hx : x < 4096) {a : ℕ} (ha : a < 8)
    (h1 : mulF2 28 (dcX x) (dcX x) = oneF2 28) (h2 : dcX x ≠ oneF2 28)
    (hc : commK (dcX x) (nthV dcHm (a + 1)) = true) : x ∈ nthL dcCl a := by
  have hs : ∀ y < 4096, Bool.rec (motive := fun _ => Bool) true
      (CFSG.KLie.CT.allN 8 fun a => Bool.rec (motive := fun _ => Bool) true
        (dcBit (nthV dcCm a) y) (commK (dcX y) (nthV dcHm (Nat.succ a))))
      (ord2K (dcX y)) = true := by
    intro y hy
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 512 ∧ y = 512 * q + r :=
      ⟨y / 512, y % 512, Nat.mod_lt _ (by norm_num), by omega⟩
    have hq : q < 8 := by omega
    interval_cases q
    · exact dcScan_spec ch733007_scan0 r hr
    · exact dcScan_spec ch733007_scan1 r hr
    · exact dcScan_spec ch733007_scan2 r hr
    · exact dcScan_spec ch733007_scan3 r hr
    · exact dcScan_spec ch733007_scan4 r hr
    · exact dcScan_spec ch733007_scan5 r hr
    · exact dcScan_spec ch733007_scan6 r hr
    · exact dcScan_spec ch733007_scan7 r hr
  have e := bIf_true' (hs x hx) (ord2K_of h1 h2)
  have e2 := bIf_true' (allN_iff'.mp e a ha) hc
  have hm := beq_iff'.mp (allN_iff'.mp ch733007_mask a ha)
  rw [← hm] at e2
  exact mem_of_testBit_dcMaskOf (testBit_of_dcBit e2)

theorem dcCand_at {a b : ℕ} (ha : 1 ≤ a) (ha9 : a < 9) (hb : b < 9) (hdet : dcDet a b = true)
    {i j : ℕ} (hi : i < (nthL dcCl (Nat.sub a 1)).length)
    (hj : j < (nthL dcCl (Nat.sub b 1)).length) :
    dcRecK [nthV dcHm a, nthV dcHm b, dcX ((nthL dcCl (Nat.sub a 1)).getD i 0),
        dcX ((nthL dcCl (Nat.sub b 1)).getD j 0)]
      (((dcNth List.nil dcDd (Nat.add (Nat.mul 9 a) b)).getD i List.nil).getD j (0, List.nil)) =
      true := by
  have hc : dcCandK dcDd a = true := by
    interval_cases a
    · exact ch733007_cand1
    · exact ch733007_cand2
    · exact ch733007_cand3
    · exact ch733007_cand4
    · exact ch733007_cand5
    · exact ch733007_cand6
    · exact ch733007_cand7
    · exact ch733007_cand8
  have e := bIf_true' (allN_iff'.mp hc b hb) hdet
  unfold dcPairK at e
  rw [strictB_eq', strictB_eq'] at e
  have e1 := dcZipK_spec e i hi
  rw [strictB_eq'] at e1
  have e2 := dcZipK_spec e1 j hj
  rw [strictB_eq'] at e2
  exact e2

theorem dcRec_cases {im : List ℕ} {r : ℕ × List (List ℕ)} (h : dcRecK im r = true) :
    dcXcK im = true ∨ (∃ ρ, Nat.beq (dcEvS im (nthL dcRl ρ)) (oneF2 28) = false) ∨
      dcDecK im (Nat.sub r.1 12) r.2 = true := by
  unfold dcRecK at h
  cases h1 : Nat.blt r.1 12
  · exact Or.inr (Or.inr (bIf_false' h h1))
  · have h' := bIf_true' h h1
    cases h2 : Nat.beq r.1 0
    · exact Or.inr (Or.inl ⟨_, notB_iff.mp (bIf_false' h' h2)⟩)
    · exact Or.inl (bIf_true' h' h2)

theorem dcLt8_spec : ∀ {w : List ℕ}, dcLt8 w = true → ∀ c ∈ w, c < 8
  | [], _ => by simp
  | c :: w, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact Nat.le_of_ble_eq_true h1
    · exact dcLt8_spec h2 c' hc'

theorem dcLt8L_spec : ∀ {L : List (List ℕ)}, dcLt8L L = true → ∀ w ∈ L, ∀ c ∈ w, c < 8
  | [], _ => by simp
  | w :: L, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro w' hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact dcLt8_spec h1
    · exact dcLt8L_spec h2 w' hw'

theorem dcRelsK_spec : ∀ {L : List (List ℕ)},
    List.rec (motive := fun _ => Bool) true
      (fun r _ ih => CFSG.KLie.CT.andB (Nat.beq (dcEvS gK r) (oneF2 28)) ih) L = true →
    ∀ w ∈ L, dcEvS gK w = oneF2 28
  | [], _ => by simp
  | w :: L, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro w' hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact beq_iff'.mp h1
    · exact dcRelsK_spec h2 w' hw'

theorem rels_at_gK (ρ : ℕ) : dcEvS gK (nthL dcRl ρ) = oneF2 28 := by
  rw [nthL_eq]
  by_cases h : ρ < dcRl.length
  · rw [List.getD_eq_getElem _ _ h]
    exact dcRelsK_spec ch733007_rels _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

theorem rels_letters (ρ : ℕ) : ∀ c ∈ nthL dcRl ρ, c < 8 := by
  rw [nthL_eq]
  by_cases h : ρ < dcRl.length
  · rw [List.getD_eq_getElem _ _ h]
    exact dcLt8L_spec (andB_iff.mp ch733007_letters).1 _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem dcDec4_spec {im : List ℕ} {d : ℕ} {R : List ℕ} {ws : List (List ℕ)} {hW : ℕ}
    (h : dcDec4K im d R ws hW = true) : d < 4 ∧ ∀ k < 4,
      (d = 0 → nthV im k = mulF2 28 (mulF2 28 hW (nthV R k)) (mulF2 28 hW hW)) ∧
      (d ≠ 0 → (∀ c ∈ nthL ws k, c < 8) ∧ wordF4 gK (nthL ws k) = nthV im k ∧
        wordF4 (nthL dcWr d) (nthL ws k) = mulF2 28 (mulF2 28 hW (nthV R k)) (mulF2 28 hW hW)) := by
  unfold dcDec4K at h
  obtain ⟨h1, h2⟩ := andB_iff.mp h
  refine ⟨Nat.le_of_ble_eq_true h1, fun k hk => ?_⟩
  have e := allN_iff'.mp h2 k hk
  rw [strictB_eq'] at e
  cases hd : Nat.beq d 0
  · have e' := bIf_false' e hd
    obtain ⟨e1, e'⟩ := andB_iff.mp e'
    obtain ⟨e2, e3⟩ := andB_iff.mp e'
    refine ⟨fun h0 => absurd (h0 ▸ hd) (by simp [Nat.beq_refl]), fun _ =>
      ⟨dcLt8_spec e1, beq_iff'.mp e2, beq_iff'.mp e3⟩⟩
  · have e' := bIf_true' e hd
    exact ⟨fun _ => beq_iff'.mp e', fun h0 => absurd (beq_iff'.mp hd) h0⟩

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (n : ℕ) (d : α) (d' : β) (hd : f d = d') :
    (l.map f).getD n d' = f (l.getD n d) := by
  rw [← hd, List.getD_map]

theorem dcWl_eq (i k : ℕ) : nthL (nthLL dcWl i) k =
    ((CFSG.Quasithin.St84.G24DC.wWords.getD i []).getD k []).map fun l => 2 * l.val := by
  have hw : dcWl = dcWords := beq_iff_eq.mp (andB_iff.mp ch733007_rows).1
  rw [nthL_eq, nthLL_eq, hw, dcWords, getD_map' _ _ _ [] [] rfl, getD_map' _ _ _ [] [] rfl]

theorem yW_map_two (w : List (Fin 4)) : yW gsB (w.map fun l => 2 * l.val) = (w.map gB0).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    change gsB.getD ((2 * l.val) / 2) 1 * yW gsB (w.map fun l => 2 * l.val) = gB0 l * (w.map gB0).prod
    rw [ih, show (2 * l.val) / 2 = l.val by omega]
    congr 1
    fin_cases l <;> rfl

theorem psi_row (hC : ChevFacts) {i : ℕ} (hi : i < 12) {k : ℕ} (hk : k < 4) :
    psi (((CFSG.Quasithin.St84.G24DC.wWords.getD i []).getD k []).map gB0).prod =
      pkMat 28 (nthV (nthL dcWr i) k) := by
  have hr := beq_iff'.mp (allN_iff'.mp (allN_iff'.mp (andB_iff.mp ch733007_rows).2 i hi) k hk)
  rw [hr, ← yW_map_two, ← dcWl_eq]
  refine (pk_wordF4 (pk_gK hC) _ ?_).symm
  intro c hc
  rw [dcWl_eq] at hc
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hc
  change (2 * l.val) / 2 < 4
  omega

theorem gsB_getD (k : Fin 4) : gsB.getD k.val 1 = gB0 k := by fin_cases k <;> rfl

theorem fin4_cases {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ k, P k := by
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem nthV_four0 (A B C D : ℕ) : nthV [A, B, C, D] 0 = A := rfl
theorem nthV_four1 (A B C D : ℕ) : nthV [A, B, C, D] 1 = B := rfl
theorem nthV_four2 (A B C D : ℕ) : nthV [A, B, C, D] 2 = C := rfl
theorem nthV_four3 (A B C D : ℕ) : nthV [A, B, C, D] 3 = D := rfl

@[expose] def hEl (s t : ℕ) : Y := k1Y ^ s * k2Y ^ t

theorem hEl_mem_H0 (s t : ℕ) : hEl s t ∈ G24M.H0 :=
  G24M.H0.mul_mem (G24M.H0.pow_mem (Subgroup.subset_closure (by simp)) s)
    (G24M.H0.pow_mem (Subgroup.subset_closure (by simp)) t)

theorem hEl_mem_M2 (hM : Facts) (s t : ℕ) : hEl s t ∈ M2 := hM.B0_le_M2 (hM.H0_le_B0 (hEl_mem_H0 s t))

theorem hEl_cube (hM : Facts) (s t : ℕ) : hEl s t ^ 3 = 1 := by
  have h1 : k1Y ^ 3 = 1 := by rw [← hM.orderOf_k1Y]; exact pow_orderOf_eq_one k1Y
  have h2 : k2Y ^ 3 = 1 := by rw [← hM.orderOf_k2Y]; exact pow_orderOf_eq_one k2Y
  rw [hEl, (hM.commute_k1Y_k2Y.pow_pow s t).mul_pow, ← pow_mul, ← pow_mul, mul_comm s 3,
    mul_comm t 3, pow_mul, pow_mul, h1, h2, one_pow, one_pow, one_mul]

theorem dcPowH0 (hM : Facts) {z : Y} (hz : z ∈ G24M.H0) :
    ∃ s t : Nat, s < 3 ∧ t < 3 ∧ z = k1Y ^ s * k2Y ^ t := by
  have h1 : k1Y ^ 3 = 1 := by rw [← hM.orderOf_k1Y]; exact pow_orderOf_eq_one k1Y
  have h2 : k2Y ^ 3 = 1 := by rw [← hM.orderOf_k2Y]; exact pow_orderOf_eq_one k2Y
  have hz' : z ∈ Subgroup.closure ({k1Y, k2Y} : Set Y) := hz
  rw [CFSG.GroupTheory.mem_closure_pair_iff_of_commute hM.commute_k1Y_k2Y] at hz'
  obtain ⟨m, n, hmn⟩ := hz'
  have hm : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
  have hn : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hm3 : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
  have hn3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  refine ⟨(m % 3).toNat, (n % 3).toNat, ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [← hmn]
    congr 1
    · calc k1Y ^ m = k1Y ^ (m % (3 : ℤ)) := zpow_eq_zpow_emod' m h1
        _ = k1Y ^ ((m % 3).toNat) := by rw [← zpow_natCast, Int.toNat_of_nonneg hm]
    · calc k2Y ^ n = k2Y ^ (n % (3 : ℤ)) := zpow_eq_zpow_emod' n h2
        _ = k2Y ^ ((n % 3).toNat) := by rw [← zpow_natCast, Int.toNat_of_nonneg hn]

theorem dcPowOne (hM : Facts) {a b : Nat} (ha : a < 3) (hb : b < 3)
    (h : k1Y ^ a * k2Y ^ b = 1) : a = 0 ∧ b = 0 := by
  have h1 : k1Y ^ 3 = 1 := by rw [← hM.orderOf_k1Y]; exact pow_orderOf_eq_one k1Y
  have h2 : k2Y ^ 3 = 1 := by rw [← hM.orderOf_k2Y]; exact pow_orderOf_eq_one k2Y
  by_cases ha0 : a = 0
  · subst ha0
    simp only [pow_zero, one_mul] at h
    by_cases hb0 : b = 0
    · exact ⟨rfl, hb0⟩
    · exfalso
      have hd : 3 ∣ b := by
        rw [← hM.orderOf_k2Y]
        exact orderOf_dvd_iff_pow_eq_one.mpr h
      rcases (show b = 1 ∨ b = 2 by omega) with rfl | rfl <;> norm_num at hd
  · by_cases hb0 : b = 0
    · subst hb0
      simp only [pow_zero, mul_one] at h
      exfalso
      have hd : 3 ∣ a := by
        rw [← hM.orderOf_k1Y]
        exact orderOf_dvd_iff_pow_eq_one.mpr h
      rcases (show a = 1 ∨ a = 2 by omega) with rfl | rfl <;> norm_num at hd
    · exfalso
      have hka : k1Y ^ a = k2Y ^ (3 - b) := by
        rw [eq_inv_of_mul_eq_one_left h]
        have hb3 : k2Y ^ b * k2Y ^ (3 - b) = 1 := by
          rw [← pow_add, show b + (3 - b) = 3 by omega, h2]
        rw [inv_eq_of_mul_eq_one_right hb3]
      have hk1 : k1Y = k2Y ^ ((3 - b) * a) := by
        calc k1Y = (k1Y ^ a) ^ a := by
              rcases (show a = 1 ∨ a = 2 by omega) with h' | h'
              · rw [h']; simp
              · rw [h', ← pow_mul, show (2 * 2 : Nat) = 4 by norm_num,
                  show (4 : Nat) = 3 + 1 by norm_num, pow_add, h1, one_mul, pow_one]
          _ = (k2Y ^ (3 - b)) ^ a := by rw [hka]
          _ = k2Y ^ ((3 - b) * a) := by rw [pow_mul]
      have hmem : k1Y ∈ Subgroup.zpowers k2Y := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.mem_closure_singleton]
        refine ⟨((3 - b) * a : ℤ), ?_⟩
        rw [show (3 - (b : ℤ)) * (a : ℤ) = (((3 - b) * a : Nat) : ℤ) by
          rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hb)]
          norm_num, zpow_natCast]
        exact hk1.symm
      have hcl : Subgroup.closure ({k1Y, k2Y} : Set Y) ≤ Subgroup.zpowers k2Y := by
        rw [Subgroup.closure_le]
        intro w hw
        rcases hw with rfl | rfl
        · exact hmem
        · exact Subgroup.mem_zpowers k2Y
      have heq : Subgroup.closure ({k1Y, k2Y} : Set Y) = Subgroup.zpowers k2Y :=
        le_antisymm hcl (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      have hcard : Nat.card (Subgroup.closure ({k1Y, k2Y} : Set Y)) = 9 := hM.card_H0
      rw [heq, Nat.card_zpowers, hM.orderOf_k2Y] at hcard
      norm_num at hcard

theorem dcNPow (hM : Facts) {n : MulAut ↥(M1 ⊓ M2)} {s t u v : Nat}
    {k1B k2B : ↥(M1 ⊓ M2)} (hk1v : (k1B : Y) = k1Y) (hk2v : (k2B : Y) = k2Y)
    (hk1 : ((n k1B : ↥(M1 ⊓ M2)) : Y) = k1Y ^ s * k2Y ^ t)
    (hk2 : ((n k2B : ↥(M1 ⊓ M2)) : Y) = k1Y ^ u * k2Y ^ v)
    {a b : Nat} (hxB : k1Y ^ a * k2Y ^ b ∈ M1 ⊓ M2) :
    ((n ⟨k1Y ^ a * k2Y ^ b, hxB⟩ : ↥(M1 ⊓ M2)) : Y) =
      k1Y ^ (s * a + u * b) * k2Y ^ (t * a + v * b) := by
  have ha : k1Y ^ a ∈ M1 ⊓ M2 :=
    hM.inf_M1_M2 ▸ hM.H0_le_B0 (G24M.H0.pow_mem (Subgroup.subset_closure (by simp)) a)
  have hb : k2Y ^ b ∈ M1 ⊓ M2 :=
    hM.inf_M1_M2 ▸ hM.H0_le_B0 (G24M.H0.pow_mem (Subgroup.subset_closure (by simp)) b)
  have hx1 : (⟨k1Y ^ a, ha⟩ : ↥(M1 ⊓ M2)) = k1B ^ a :=
    Subtype.ext (by rw [Subgroup.coe_pow, hk1v])
  have hx2 : (⟨k2Y ^ b, hb⟩ : ↥(M1 ⊓ M2)) = k2B ^ b :=
    Subtype.ext (by rw [Subgroup.coe_pow, hk2v])
  have hsplit : (⟨k1Y ^ a * k2Y ^ b, hxB⟩ : ↥(M1 ⊓ M2)) =
      (⟨k1Y ^ a, ha⟩ : ↥(M1 ⊓ M2)) * ⟨k2Y ^ b, hb⟩ := Subtype.ext rfl
  have h1 : ((n (⟨k1Y ^ a, ha⟩ : ↥(M1 ⊓ M2)) : ↥(M1 ⊓ M2)) : Y) =
      (k1Y ^ s * k2Y ^ t) ^ a := by
    rw [hx1, map_pow, Subgroup.coe_pow, hk1]
  have h2 : ((n (⟨k2Y ^ b, hb⟩ : ↥(M1 ⊓ M2)) : ↥(M1 ⊓ M2)) : Y) =
      (k1Y ^ u * k2Y ^ v) ^ b := by
    rw [hx2, map_pow, Subgroup.coe_pow, hk2]
  rw [hsplit, map_mul, Subgroup.coe_mul, h1, h2,
    (hM.commute_k1Y_k2Y.pow_pow s t).mul_pow a,
    (hM.commute_k1Y_k2Y.pow_pow u v).mul_pow b, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
    (hM.commute_k1Y_k2Y.symm.pow_pow (t * a) (u * b)).mul_mul_mul_comm
      (k1Y ^ (s * a)) (k2Y ^ (v * b)), ← pow_add, ← pow_add]

theorem dcDetNe (hM : Facts) {n : MulAut ↥(M1 ⊓ M2)} {s t u v : Nat}
    {k1B k2B : ↥(M1 ⊓ M2)} (hk1v : (k1B : Y) = k1Y) (hk2v : (k2B : Y) = k2Y)
    (hs : s < 3) (ht : t < 3) (hu : u < 3) (hv : v < 3)
    (hk1 : ((n k1B : ↥(M1 ⊓ M2)) : Y) = k1Y ^ s * k2Y ^ t)
    (hk2 : ((n k2B : ↥(M1 ⊓ M2)) : Y) = k1Y ^ u * k2Y ^ v) :
    (s * v) % 3 ≠ (t * u) % 3 := by
  intro hmod
  have hsum : ∀ r : Nat, r < 3 → (r + (3 - r) % 3) % 3 = 0 := by
    intro r hr
    interval_cases r <;> decide
  have key : ∀ a b : Nat, a < 3 → b < 3 → (a, b) ≠ (0, 0) →
      (s * a + u * b) % 3 = 0 → (t * a + v * b) % 3 = 0 → False := by
    intro a b ha hb hne0 hca hcb
    have hxH0 : k1Y ^ a * k2Y ^ b ∈ G24M.H0 := by
      have e : k1Y ^ a * k2Y ^ b = hEl a b := rfl
      rw [e]
      exact hEl_mem_H0 a b
    have hxB : k1Y ^ a * k2Y ^ b ∈ M1 ⊓ M2 := hM.inf_M1_M2 ▸ hM.H0_le_B0 hxH0
    have hxne : k1Y ^ a * k2Y ^ b ≠ 1 := by
      intro hx1
      exact hne0 (Prod.ext (dcPowOne hM ha hb hx1).1 (dcPowOne hM ha hb hx1).2)
    have hred1 : k1Y ^ (s * a + u * b) = 1 := by
      rw [← pow_mod_orderOf k1Y (s * a + u * b), hM.orderOf_k1Y, hca, pow_zero]
    have hred2 : k2Y ^ (t * a + v * b) = 1 := by
      rw [← pow_mod_orderOf k2Y (t * a + v * b), hM.orderOf_k2Y, hcb, pow_zero]
    have hn1 : ((n ⟨k1Y ^ a * k2Y ^ b, hxB⟩ : ↥(M1 ⊓ M2)) : Y) = 1 := by
      rw [dcNPow hM hk1v hk2v hk1 hk2 hxB, hred1, hred2, one_mul]
    have h2e : (n (⟨k1Y ^ a * k2Y ^ b, hxB⟩ : ↥(M1 ⊓ M2)) : ↥(M1 ⊓ M2)) = 1 :=
      Subtype.ext hn1
    have hxe : (⟨k1Y ^ a * k2Y ^ b, hxB⟩ : ↥(M1 ⊓ M2)) = 1 :=
      n.injective (by rw [h2e, map_one])
    exact hxne (congrArg Subtype.val hxe)
  by_cases htv : t = 0 ∧ v = 0
  · obtain ⟨rfl, rfl⟩ := htv
    have hk2' : ((n k2B : ↥(M1 ⊓ M2)) : Y) = k1Y ^ u := by
      simpa using hk2
    have hu0 : u ≠ 0 := by
      intro hu0
      have hn2 : ((n k2B : ↥(M1 ⊓ M2)) : Y) = 1 := by
        rw [hk2', hu0, pow_zero]
      have h2e : (n k2B : ↥(M1 ⊓ M2)) = 1 := Subtype.ext hn2
      have hk2e : k2B = 1 := n.injective (by rw [h2e, map_one])
      have hk2Y : k2Y = 1 := by rw [← hk2v, hk2e]; rfl
      have hord : orderOf (1 : Y) = 3 := by rw [← hk2Y]; exact hM.orderOf_k2Y
      rw [orderOf_one] at hord
      omega
    refine key u ((3 - s) % 3) hu (Nat.mod_lt _ (by norm_num)) ?_ ?_ ?_
    · intro h
      exact hu0 (by simpa using congrArg Prod.fst h)
    · have he : s * u + u * ((3 - s) % 3) = u * (s + (3 - s) % 3) := by ring
      rw [he, Nat.mul_mod, hsum s hs]
      simp
    · simp
  · refine key v ((3 - t) % 3) hv (Nat.mod_lt _ (by norm_num)) ?_ ?_ ?_
    · intro h
      apply htv
      have hv0 : v = 0 := by simpa using congrArg Prod.fst h
      have hb0 : (3 - t) % 3 = 0 := by simpa using congrArg Prod.snd h
      have ht0 : t = 0 := by
        interval_cases t
        · rfl
        · norm_num at hb0
        · norm_num at hb0
      exact ⟨ht0, hv0⟩
    · have htc : (t + (3 - t) % 3) % 3 = 0 := hsum t ht
      have hutc : ((u * t) % 3 + (u * ((3 - t) % 3)) % 3) % 3 = 0 := by
        rw [← Nat.add_mod, ← Nat.mul_add, Nat.mul_mod, htc]
        simp
      rw [Nat.add_mod, hmod, Nat.mul_comm t u]
      exact hutc
    · have htc : (t + (3 - t) % 3) % 3 = 0 := hsum t ht
      have he : t * v + v * ((3 - t) % 3) = v * (t + (3 - t) % 3) := by ring
      rw [he, Nat.mul_mod, htc]
      simp

theorem dcDet_of {s t u v : ℕ} (hs : s < 3) (ht : t < 3) (hu : u < 3) (hv : v < 3)
    (h : (s * v) % 3 ≠ (t * u) % 3) : dcDet (3 * s + t) (3 * u + v) = true := by
  have e1 : Nat.div (3 * s + t) 3 = s := by change (3 * s + t) / 3 = s; omega
  have e2 : Nat.mod (3 * s + t) 3 = t := by change (3 * s + t) % 3 = t; omega
  have e3 : Nat.div (3 * u + v) 3 = u := by change (3 * u + v) / 3 = u; omega
  have e4 : Nat.mod (3 * u + v) 3 = v := by change (3 * u + v) % 3 = v; omega
  unfold dcDet
  rw [e1, e2, e3, e4]
  cases hb : Nat.beq (Nat.mod (Nat.mul s v) 3) (Nat.mod (Nat.mul t u) 3) with
  | false => rfl
  | true => exact absurd (beq_iff'.mp hb) h

theorem coe_evM (gB : Fin 4 → ↥(M1 ⊓ M2)) (w : List ℕ) :
    ((evM gB w : ↥(M1 ⊓ M2)) : Y) = evM (fun k => (gB k : Y)) w :=
  map_evM (M1 ⊓ M2).subtype gB w

theorem n_evM (n : MulAut ↥(M1 ⊓ M2)) (gB : Fin 4 → ↥(M1 ⊓ M2)) (w : List ℕ) :
    ((n (evM gB w) : ↥(M1 ⊓ M2)) : Y) = evM (fun k => ((n (gB k) : ↥(M1 ⊓ M2)) : Y)) w := by
  have e := congrArg Subtype.val (map_evM n.toMonoidHom gB w)
  rw [coe_evM] at e
  exact e

theorem ev_one_of (hC : ChevFacts) (n : MulAut ↥(M1 ⊓ M2)) (gB : Fin 4 → ↥(M1 ⊓ M2))
    (hgB : ∀ k, (gB k : Y) = gB0 k) {im : List ℕ}
    (hz : ∀ k : Fin 4, psi ((n (gB k) : ↥(M1 ⊓ M2)) : Y) = pkMat 28 (nthV im k.val))
    {w : List ℕ} (hw : ∀ c ∈ w, c < 8) (h : dcEvS gK w = oneF2 28) : dcEvS im w = oneF2 28 := by
  have h2 : psi ((evM gB w : ↥(M1 ⊓ M2)) : Y) = 1 := by
    rw [coe_evM, pk_dcEvS hC (fun k => by rw [hgB, psi_gB0 hC]) w hw, h, pkMat_oneF2]
  have h3 : evM gB w = 1 := Subtype.ext (psi_injective hC (by rw [h2, OneMemClass.coe_one, map_one]))
  have h4 := n_evM n gB w
  rw [h3, map_one, OneMemClass.coe_one] at h4
  refine (pk_one_iff (dcEvS_lt _ _)).mp ?_
  rw [← pk_dcEvS hC hz w hw, ← h4, map_one]

theorem xc_of (hC : ChevFacts) (n : MulAut ↥(M1 ⊓ M2)) (gB : Fin 4 → ↥(M1 ⊓ M2))
    (hgB : ∀ k, (gB k : Y) = gB0 k) {im : List ℕ}
    (hz : ∀ k : Fin 4, psi ((n (gB k) : ↥(M1 ⊓ M2)) : Y) = pkMat 28 (nthV im k.val)) :
    dcXcK im = false := by
  have hw := dcLt8_spec (andB_iff.mp ch733007_letters).2
  cases hk : dcXcK im with
  | false => rfl
  | true =>
    exfalso
    unfold dcXcK at hk
    rw [strictB_eq'] at hk
    have hsq := beq_iff'.mp hk
    have h1 : psi ((n (evM gB dcXh ^ 2) : ↥(M1 ⊓ M2)) : Y) = 1 := by
      rw [map_pow, Subgroup.coe_pow, map_pow, n_evM, pk_dcEvS hC hz _ hw, pow_two, ← pkMat_mulF2, hsq,
        pkMat_oneF2]
    have h2 : evM gB dcXh ^ 2 = 1 := by
      have h1' : (n (evM gB dcXh ^ 2) : ↥(M1 ⊓ M2)) = 1 :=
        Subtype.ext (psi_injective hC (by rw [h1, OneMemClass.coe_one, map_one]))
      exact n.injective (by rw [h1', map_one])
    have h3 : psi ((evM gB dcXh ^ 2 : ↥(M1 ⊓ M2)) : Y) = 1 := by
      rw [h2, OneMemClass.coe_one, map_one]
    rw [Subgroup.coe_pow, map_pow, coe_evM, pk_dcEvS hC (fun k => by rw [hgB, psi_gB0 hC]) _ hw,
      pow_two, ← pkMat_mulF2] at h3
    have h4 := (pk_one_iff (mulF2_lt' _ _)).mp h3
    have h5 : dcXcK gK = true := by
      unfold dcXcK
      rw [strictB_eq', h4, Nat.beq_refl]
    have h6 := ch733007_xc
    rw [h5] at h6
    exact Bool.noConfusion h6

theorem psi_W2_gB0 (hC : ChevFacts) (W : Witnesses) (j : Fin 8) (k : Fin 4) (hk : gB0 k ∈ M2) :
    psi ((W.W2 j ⟨gB0 k, hk⟩ : ↥M2) : Y) = pkMat 28 (nthV (nthL dcWr (4 + j.val)) k.val) := by
  rw [W.W2_gB0 j k _ rfl]
  exact psi_row hC (by omega) k.2

theorem psi_W1_gB0 (hC : ChevFacts) (W : Witnesses) (i : Fin 4) (k : Fin 4) (hk : gB0 k ∈ M1) :
    psi ((W.W1 i ⟨gB0 k, hk⟩ : ↥M1) : Y) = pkMat 28 (nthV (nthL dcWr i.val) k.val) := by
  rw [W.W1_gB0 i k _ rfl]
  exact psi_row hC (by omega) k.2

@[expose] def w1L (hM : Facts) (W : Witnesses) (i : Fin 4) : List Y :=
  List.ofFn fun k : Fin 4 => ((W.W1 i ⟨gB0 k, hM.B0_le_M1 (hM.gB0_mem_B0 k)⟩ : ↥M1) : Y)

theorem gB0_mem_M1' (hM : Facts) (g : Y) (hg : g ∈ gsB) : g ∈ M1 := by
  simp only [gsB, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact hM.B0_le_M1 (hM.gB0_mem_B0 0)
  · exact hM.B0_le_M1 (hM.gB0_mem_B0 1)
  · exact hM.B0_le_M1 (hM.gB0_mem_B0 2)
  · exact hM.B0_le_M1 (hM.gB0_mem_B0 3)

theorem W1_yW (hM : Facts) (W : Witnesses) (i : Fin 4) :
    ∀ (u : List ℕ), (∀ c ∈ u, c < 8) → ∀ (hm : yW gsB u ∈ M1),
      ((W.W1 i ⟨yW gsB u, hm⟩ : ↥M1) : Y) = yW (w1L hM W i) u
  | [], _, hm => by
    have e : (⟨yW gsB [], hm⟩ : ↥M1) = 1 := Subtype.ext rfl
    rw [e, map_one]
    rfl
  | c :: u, hu, hm => by
    have hc : c / 2 < 4 := by have := hu c (by simp); omega
    have hmem1 : gB0 ⟨c / 2, hc⟩ ∈ M1 := hM.B0_le_M1 (hM.gB0_mem_B0 _)
    have hmemu : yW gsB u ∈ M1 := yW_mem (gB0_mem_M1' hM) u
    have hsplit : (⟨yW gsB (c :: u), hm⟩ : ↥M1) = ⟨gB0 ⟨c / 2, hc⟩, hmem1⟩ * ⟨yW gsB u, hmemu⟩ := by
      apply Subtype.ext
      change gsB.getD (c / 2) 1 * yW gsB u = gB0 ⟨c / 2, hc⟩ * yW gsB u
      rw [gsB_getD ⟨c / 2, hc⟩]
    rw [hsplit, map_mul, Subgroup.coe_mul, W1_yW hM W i u (fun c' hc' => hu c' (by simp [hc'])) hmemu]
    change _ = (w1L hM W i).getD (c / 2) 1 * yW (w1L hM W i) u
    rw [w1L, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_ofFn]

theorem psi_yW_w1L (hC : ChevFacts) (hM : Facts) (W : Witnesses) (i : Fin 4) (u : List ℕ)
    (hu : ∀ c ∈ u, c < 8) : psi (yW (w1L hM W i) u) = pkMat 28 (wordF4 (nthL dcWr i.val) u) := by
  refine (pk_wordF4 (fun k hk => ?_) u (fun c hc => ?_)).symm
  · have hk4 : k < 4 := by simpa [w1L] using hk
    rw [w1L, List.getD_eq_getElem (List.ofFn _) 1 (by simpa using hk4), List.getElem_ofFn,
      psi_W1_gB0 hC W i ⟨k, hk4⟩, nthV_eq]
  · have := hu c hc
    simp only [w1L, List.length_ofFn]
    omega

theorem psi_W2_tgt (hC : ChevFacts) (hM : Facts) (W : Witnesses) (j : Fin 8) (s t : ℕ) (k : Fin 4)
    (hm : hEl s t * gB0 k * (hEl s t)⁻¹ ∈ M2) :
    psi ((W.W2 j ⟨hEl s t * gB0 k * (hEl s t)⁻¹, hm⟩ : ↥M2) : Y) =
      pkMat 28 (mulF2 28 (mulF2 28 (mulF2 28 (dcPow (nthV (nthL dcWr (4 + j.val)) 0) s)
          (dcPow (nthV (nthL dcWr (4 + j.val)) 1) t)) (nthV (nthL dcWr (4 + j.val)) k.val))
        (mulF2 28 (mulF2 28 (dcPow (nthV (nthL dcWr (4 + j.val)) 0) s)
          (dcPow (nthV (nthL dcWr (4 + j.val)) 1) t))
          (mulF2 28 (dcPow (nthV (nthL dcWr (4 + j.val)) 0) s)
          (dcPow (nthV (nthL dcWr (4 + j.val)) 1) t)))) := by
  let h' : ↥M2 := ⟨hEl s t, hEl_mem_M2 hM s t⟩
  let g' : ↥M2 := ⟨gB0 k, hM.B0_le_M2 (hM.gB0_mem_B0 k)⟩
  let k1' : ↥M2 := ⟨gB0 0, hM.B0_le_M2 (hM.gB0_mem_B0 0)⟩
  let k2' : ↥M2 := ⟨gB0 1, hM.B0_le_M2 (hM.gB0_mem_B0 1)⟩
  have e : (⟨hEl s t * gB0 k * (hEl s t)⁻¹, hm⟩ : ↥M2) = h' * g' * h'⁻¹ := Subtype.ext rfl
  have eh : h' = k1' ^ s * k2' ^ t := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    rfl)
  have hW : psi ((W.W2 j h' : ↥M2) : Y) = pkMat 28 (mulF2 28 (dcPow (nthV (nthL dcWr (4 + j.val)) 0) s)
      (dcPow (nthV (nthL dcWr (4 + j.val)) 1) t)) := by
    rw [eh, map_mul, map_pow, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, map_mul,
      psi_pow_dcPow (psi_W2_gB0 hC W j 0 _), psi_pow_dcPow (psi_W2_gB0 hC W j 1 _), pkMat_mulF2]
    rfl
  have h3 : (W.W2 j h') ^ 3 = 1 := by
    rw [← map_pow]
    have : h' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hEl_cube hM s t)
    rw [this, map_one]
  have hinv : (W.W2 j h')⁻¹ = W.W2 j h' * W.W2 j h' := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, ← pow_two, ← pow_succ, h3]
  rw [e, map_mul, map_mul, map_inv, hinv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    map_mul, map_mul, map_mul, hW, psi_W2_gB0 hC W j k _]
  simp only [pkMat_mulF2]

theorem tgt_mem (hM : Facts) (s t : ℕ) (k : Fin 4) : hEl s t * gB0 k * (hEl s t)⁻¹ ∈ M2 :=
  M2.mul_mem (M2.mul_mem (hEl_mem_M2 hM s t) (hM.B0_le_M2 (hM.gB0_mem_B0 k)))
    (M2.inv_mem (hEl_mem_M2 hM s t))

theorem closure_gB_top (hM : Facts) (gB : Fin 4 → ↥(M1 ⊓ M2)) (hgB : ∀ k, (gB k : Y) = gB0 k) :
    Subgroup.closure (Set.range gB) = ⊤ := by
  apply Subgroup.map_injective (f := Subgroup.subtype (M1 ⊓ M2)) Subtype.coe_injective
  rw [show Subgroup.map (Subgroup.subtype (M1 ⊓ M2)) (Subgroup.closure (Set.range gB)) =
      Subgroup.closure (Subgroup.subtype (M1 ⊓ M2) '' Set.range gB) from
        MonoidHom.map_closure _ _,
    Subgroup.map_top, Subgroup.range_subtype]
  have himg : Subtype.val '' Set.range gB = Set.range gB0 := by
    ext y
    constructor
    · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (hgB k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨gB k, ⟨k, rfl⟩, hgB k⟩
  change Subgroup.closure (Subtype.val '' Set.range gB) = M1 ⊓ M2
  rw [himg, hM.closure_gB0]
  exact hM.inf_M1_M2.symm

theorem decomp_of_gens (hM : Facts) (W : Witnesses) (n : MulAut ↥(M1 ⊓ M2))
    (gB : Fin 4 → ↥(M1 ⊓ M2)) (hgB : ∀ k, (gB k : Y) = gB0 k) (a : MulAut ↥M1)
    (ha : ∀ m : ↥M1, (m : Y) ∈ M2 ↔ ((a m : ↥M1) : Y) ∈ M2) (j : Fin 8) (s t : ℕ)
    (hk : ∀ k : Fin 4, ((a (Subgroup.inclusion inf_le_left (n (gB k))) : ↥M1) : Y) =
      ((W.W2 j ⟨hEl s t * gB0 k * (hEl s t)⁻¹, tgt_mem hM s t k⟩ : ↥M2) : Y)) :
    ∃ (a : MulAut ↥M1) (j : Fin 8) (h : Y), h ∈ G24M.H0 ∧
      (∀ m : ↥M1, (m : Y) ∈ M2 ↔ ((a m : ↥M1) : Y) ∈ M2) ∧
      ∀ (x : ↥(M1 ⊓ M2)) (m₁ : ↥M1) (m₂ : ↥M2), (m₁ : Y) = ((n x : ↥(M1 ⊓ M2)) : Y) →
        (m₂ : Y) = h * (x : Y) * h⁻¹ → ((a m₁ : ↥M1) : Y) = ((W.W2 j m₂ : ↥M2) : Y) := by
  let incB1 : ↥(M1 ⊓ M2) →* ↥M1 := Subgroup.inclusion inf_le_left
  let incB2 : ↥(M1 ⊓ M2) →* ↥M2 := Subgroup.inclusion inf_le_right
  let hM2m : ↥M2 := ⟨hEl s t, hEl_mem_M2 hM s t⟩
  let F := (Subgroup.subtype M1).comp (a.toMonoidHom.comp (incB1.comp n.toMonoidHom))
  let G := (Subgroup.subtype M2).comp
    ((W.W2 j).toMonoidHom.comp ((MulAut.conj hM2m).toMonoidHom.comp incB2))
  have hconj : ∀ x : ↥(M1 ⊓ M2), ((MulAut.conj hM2m (incB2 x) : ↥M2) : Y) =
      hEl s t * (x : Y) * (hEl s t)⁻¹ := by
    intro x
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hFG : F = G := by
    apply MonoidHom.eq_of_eqOn_dense (closure_gB_top hM gB hgB)
    intro y hy
    obtain ⟨k, rfl⟩ := hy
    have hx : MulAut.conj hM2m (incB2 (gB k)) = ⟨hEl s t * gB0 k * (hEl s t)⁻¹, tgt_mem hM s t k⟩ :=
      Subtype.ext (by rw [hconj, hgB])
    change ((a (incB1 (n (gB k))) : ↥M1) : Y) =
      ((W.W2 j (MulAut.conj hM2m (incB2 (gB k)) : ↥M2) : ↥M2) : Y)
    rw [hx]
    exact hk k
  refine ⟨a, j, hEl s t, hEl_mem_H0 s t, ha, ?_⟩
  intro x m1 m2 hm1 hm2
  have hm1_eq : m1 = incB1 (n x) := Subtype.ext hm1
  have hm2_eq : m2 = (MulAut.conj hM2m (incB2 x) : ↥M2) := Subtype.ext (by rw [hm2, hconj])
  subst m1
  subst m2
  exact congrArg (fun f : ↥(M1 ⊓ M2) →* Y => f x) hFG

theorem inv_facts (hC : ChevFacts) {w : Y} {X : ℕ} (hw : psi w = pkMat 28 X)
    (hX : X < 2 ^ (28 * 28)) (h2 : w * w = 1) (h1 : w ≠ 1) :
    mulF2 28 X X = oneF2 28 ∧ X ≠ oneF2 28 := by
  refine ⟨(pk_one_iff (mulF2_lt' _ _)).mp (by rw [pkMat_mulF2, ← hw, ← map_mul, h2, map_one]), ?_⟩
  intro hX1
  apply h1
  apply psi_injective hC
  rw [hw, hX1, pkMat_oneF2, map_one]

theorem comm_of (hC : ChevFacts) {w h : Y} {X H : ℕ} (hw : psi w = pkMat 28 X)
    (hh : psi h = pkMat 28 H) (hc : w * h = h * w) : commK X H = true := by
  have e : pkMat 28 (mulF2 28 X H) = pkMat 28 (mulF2 28 H X) := by
    rw [pkMat_mulF2, pkMat_mulF2, ← hw, ← hh, ← map_mul, ← map_mul, hc]
  have e2 := eq_of_pk (mulF2_lt' _ _) (mulF2_lt' _ _) e
  unfold commK
  rw [e2]
  exact Nat.beq_refl _

theorem psi_hEl (hC : ChevFacts) {s t : ℕ} (hs : s < 3) (ht : t < 3) :
    psi (k1Y ^ s * k2Y ^ t) = pkMat 28 (nthV dcHm (3 * s + t)) := by
  have e := beq_iff'.mp (allN_iff'.mp (allN_iff'.mp ch733007_h s hs) t ht)
  rw [show 3 * s + t = Nat.add (Nat.mul 3 s) t from rfl, e, map_mul, psi_pow_dcPow (psi_k1 hC),
    psi_pow_dcPow (psi_k2 hC), pkMat_mulF2]

theorem decompFacts (hC : ChevFacts) (hM : Facts) (W : Witnesses) : DecompFacts W := by
  refine ⟨fun n hn => ?_⟩
  have hB : ∀ k : Fin 4, gB0 k ∈ M1 ⊓ M2 := fun k => hM.inf_M1_M2 ▸ hM.gB0_mem_B0 k
  let gB : Fin 4 → ↥(M1 ⊓ M2) := fun k => ⟨gB0 k, hB k⟩
  have hgB : ∀ k, (gB k : Y) = gB0 k := fun k => rfl
  have hk1H0 : (gB 0 : Y) ∈ G24M.H0 := Subgroup.subset_closure (Set.mem_insert k1Y _)
  have hk2H0 : (gB 1 : Y) ∈ G24M.H0 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem k1Y (Set.mem_singleton k2Y))
  obtain ⟨s, t, hs, ht, hn1⟩ := dcPowH0 hM (hn (gB 0) hk1H0)
  obtain ⟨u, v, hu, hv, hn2⟩ := dcPowH0 hM (hn (gB 1) hk2H0)
  have hdet := dcDetNe hM (n := n) (k1B := gB 0) (k2B := gB 1) rfl rfl hs ht hu hv hn1 hn2
  have hz0 : psi ((n (gB 0) : ↥(M1 ⊓ M2)) : Y) = pkMat 28 (nthV dcHm (3 * s + t)) := by
    rw [hn1]
    exact psi_hEl hC hs ht
  have hz1 : psi ((n (gB 1) : ↥(M1 ⊓ M2)) : Y) = pkMat 28 (nthV dcHm (3 * u + v)) := by
    rw [hn2]
    exact psi_hEl hC hu hv
  have hBmem : ∀ k, ((n (gB k) : ↥(M1 ⊓ M2)) : Y) ∈ B0 := fun k => hM.inf_M1_M2 ▸ (n (gB k)).2
  have hord2 : ∀ k : Fin 4, orderOf (gB0 k) = 2 →
      ((n (gB k) : ↥(M1 ⊓ M2)) : Y) * ((n (gB k) : ↥(M1 ⊓ M2)) : Y) = 1 ∧
        ((n (gB k) : ↥(M1 ⊓ M2)) : Y) ≠ 1 := by
    intro k hk
    have hg : gB k * gB k = 1 := Subtype.ext (by
      change gB0 k * gB0 k = 1
      rw [← pow_two, ← hk]
      exact pow_orderOf_eq_one _)
    constructor
    · rw [← Subgroup.coe_mul, ← map_mul, hg, map_one]
      rfl
    · intro h1
      have e1 : n (gB k) = 1 := Subtype.ext h1
      have e2 : gB k = 1 := n.injective (by rw [e1, map_one])
      have e3 : gB0 k = 1 := congrArg Subtype.val e2
      rw [e3, orderOf_one] at hk
      omega
  obtain ⟨ha2, ha2'⟩ := hord2 2 hM.orderOf_xaY
  obtain ⟨hb2, hb2'⟩ := hord2 3 hM.orderOf_xbY
  obtain ⟨x, hx, hpx⟩ := exists_pos_of_sq hC hM (hBmem 2) ha2
  obtain ⟨y, hy, hpy⟩ := exists_pos_of_sq hC hM (hBmem 3) hb2
  obtain ⟨hx1, hx2⟩ := inv_facts hC hpx (mulF2_lt' _ _) ha2 ha2'
  obtain ⟨hy1, hy2⟩ := inv_facts hC hpy (mulF2_lt' _ _) hb2 hb2'
  have hc02 : commK (dcX x) (nthV dcHm (3 * s + t)) = true := by
    refine comm_of hC hpx hz0 ?_
    have e : gB 2 * gB 0 = gB 0 * gB 2 := Subtype.ext hM.commute_k1Y_xaY.eq.symm
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, e]
  have hc13 : commK (dcX y) (nthV dcHm (3 * u + v)) = true := by
    refine comm_of hC hpy hz1 ?_
    have e : gB 3 * gB 1 = gB 1 * gB 3 := Subtype.ext hM.commute_k2Y_xbY.eq.symm
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, e]
  have ha1 : 1 ≤ 3 * s + t := by
    by_contra h
    obtain rfl : s = 0 := by omega
    obtain rfl : t = 0 := by omega
    simp at hdet
  have hb1 : 1 ≤ 3 * u + v := by
    by_contra h
    obtain rfl : u = 0 := by omega
    obtain rfl : v = 0 := by omega
    simp at hdet
  have hxL : x ∈ nthL dcCl (Nat.sub (3 * s + t) 1) := by
    have e : Nat.sub (3 * s + t) 1 + 1 = 3 * s + t := by
      change 3 * s + t - 1 + 1 = 3 * s + t
      omega
    refine mem_cl hx (by change 3 * s + t - 1 < 8; omega) hx1 hx2 ?_
    rw [e]
    exact hc02
  have hyL : y ∈ nthL dcCl (Nat.sub (3 * u + v) 1) := by
    have e : Nat.sub (3 * u + v) 1 + 1 = 3 * u + v := by
      change 3 * u + v - 1 + 1 = 3 * u + v
      omega
    refine mem_cl hy (by change 3 * u + v - 1 < 8; omega) hy1 hy2 ?_
    rw [e]
    exact hc13
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxL
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hyL
  have hcand := dcCand_at ha1 (by omega) (by omega) (dcDet_of hs ht hu hv hdet) hi hj
  rw [List.getD_eq_getElem _ _ hi, hix, List.getD_eq_getElem _ _ hj, hjy] at hcand
  obtain ⟨r, hr⟩ : ∃ r, dcRecK [nthV dcHm (3 * s + t), nthV dcHm (3 * u + v), dcX x, dcX y] r = true :=
    ⟨_, hcand⟩
  have hz : ∀ k : Fin 4, psi ((n (gB k) : ↥(M1 ⊓ M2)) : Y) =
      pkMat 28 (nthV [nthV dcHm (3 * s + t), nthV dcHm (3 * u + v), dcX x, dcX y] k.val) := by
    refine fin4_cases ?_ ?_ ?_ ?_
    · change _ = pkMat 28 (nthV [nthV dcHm (3 * s + t), nthV dcHm (3 * u + v), dcX x, dcX y] 0)
      rw [nthV_four0]
      exact hz0
    · change _ = pkMat 28 (nthV [nthV dcHm (3 * s + t), nthV dcHm (3 * u + v), dcX x, dcX y] 1)
      rw [nthV_four1]
      exact hz1
    · change _ = pkMat 28 (nthV [nthV dcHm (3 * s + t), nthV dcHm (3 * u + v), dcX x, dcX y] 2)
      rw [nthV_four2]
      exact hpx
    · change _ = pkMat 28 (nthV [nthV dcHm (3 * s + t), nthV dcHm (3 * u + v), dcX x, dcX y] 3)
      rw [nthV_four3]
      exact hpy
  rcases dcRec_cases hr with hk | ⟨ρ, hρ⟩ | hdec
  · rw [xc_of hC n gB hgB hz] at hk
    exact absurd hk (by simp)
  · rw [ev_one_of hC n gB hgB hz (rels_letters ρ) (rels_at_gK ρ), Nat.beq_refl] at hρ
    exact absurd hρ (by simp)
  · unfold dcDecK at hdec
    generalize Nat.sub r.1 12 = f at hdec
    generalize r.2 = ws at hdec
    obtain ⟨hd4, hk⟩ := dcDec4_spec hdec
    let jF : Fin 8 := ⟨Nat.mod (Nat.div f 9) 8, Nat.mod_lt _ (by norm_num)⟩
    have hT : ∀ k : Fin 4,
        psi ((W.W2 jF ⟨hEl (Nat.mod (Nat.div f 3) 3) (Nat.mod f 3) * gB0 k *
          (hEl (Nat.mod (Nat.div f 3) 3) (Nat.mod f 3))⁻¹,
          tgt_mem hM (Nat.mod (Nat.div f 3) 3) (Nat.mod f 3) k⟩ : ↥M2) : Y) =
        pkMat 28 (mulF2 28 (mulF2 28 (mulF2 28
          (dcPow (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) 0) (Nat.mod (Nat.div f 3) 3))
          (dcPow (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) 1) (Nat.mod f 3)))
          (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) k.val))
          (mulF2 28 (mulF2 28
            (dcPow (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) 0) (Nat.mod (Nat.div f 3) 3))
            (dcPow (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) 1) (Nat.mod f 3)))
            (mulF2 28
              (dcPow (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) 0) (Nat.mod (Nat.div f 3) 3))
              (dcPow (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) 1) (Nat.mod f 3))))) :=
      fun k => psi_W2_tgt hC hM W jF _ _ k _
    by_cases hd : Nat.div f 72 = 0
    · refine decomp_of_gens hM W n gB hgB 1 (fun m => by rw [MulAut.one_apply]) jF
        (Nat.mod (Nat.div f 3) 3) (Nat.mod f 3) (fun k => ?_)
      rw [MulAut.one_apply]
      refine psi_injective hC ?_
      rw [hT k]
      have e := (hk k.val k.2).1 hd
      rw [← e]
      exact hz k
    · have hi1 : Nat.div f 72 < 4 := hd4
      refine decomp_of_gens hM W n gB hgB (W.W1 ⟨Nat.div f 72, hi1⟩) (W.W1_mem _) jF
        (Nat.mod (Nat.div f 3) 3) (Nat.mod f 3) (fun k => ?_)
      obtain ⟨hl, hw1, hw2⟩ := (hk k.val k.2).2 hd
      have hl' : ∀ c ∈ nthL ws k.val, c / 2 < gsB.length := fun c hc => by
        have := hl c hc
        change c / 2 < 4
        omega
      have hmem : yW gsB (nthL ws k.val) ∈ M1 := yW_mem (gB0_mem_M1' hM) _
      have hzk : ((n (gB k) : ↥(M1 ⊓ M2)) : Y) = yW gsB (nthL ws k.val) :=
        psi_injective hC (by rw [hz k, ← hw1]; exact pk_wordF4 (pk_gK hC) _ hl')
      have e : (Subgroup.inclusion inf_le_left (n (gB k)) : ↥M1) = ⟨yW gsB (nthL ws k.val), hmem⟩ :=
        Subtype.ext hzk
      rw [e, W1_yW hM W _ _ hl hmem]
      refine psi_injective hC ?_
      rw [psi_yW_w1L hC hM W _ _ hl, hT k]
      exact congrArg (pkMat 28) hw2

end CFSG.KD.G24B
