module

public import Certificates.Kernel.J4NP7850.Checks
public import CFSG.Certificates.Kernel.J4NP7850.Spec
public import CFSG.Quasithin.Vol2.KGFactC31J4M4KW3

public section

namespace CertificateChecks.KernelJ4NP7850

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31.J4M4 CFSG.KD.J4NP7850
  CFSG.KS.J4NP7850

@[expose] noncomputable def laneP (T j : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul 11 j)) 2047

theorem actP_go (T c : Nat) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc
        (Nat.xor acc (Nat.land (Nat.shiftRight T (Nat.mul 11 j)) 2047))
        (Nat.beq (Nat.land (Nat.shiftRight c j) 1) 1)) n = rowsXor (laneP T) n c
  | 0 => rfl
  | n + 1 => by
    change Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1) = _
    rw [land_shiftRight_one, rowsXor_succ, ← actP_go T c n]
    cases c.testBit n
    · exact (Nat.xor_zero _).symm
    · rfl

theorem actP_eq_rowsXor (T c : Nat) : actP T c = rowsXor (laneP T) 11 c := actP_go T c 11

theorem rowsXor_congr {r r' : Nat → Nat} (h : ∀ j < 11, r j = r' j) (c : Nat) :
    rowsXor r 11 c = rowsXor r' 11 c := by
  have key : ∀ m ≤ 11, rowsXor r m c = rowsXor r' m c := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [rowsXor_succ, rowsXor_succ, ih (by omega), h m (by omega)]
  exact key 11 le_rfl

theorem rowsXor_xor (r : Nat → Nat) : ∀ (m x y : Nat),
    rowsXor r m (x ^^^ y) = rowsXor r m x ^^^ rowsXor r m y
  | 0, x, y => by rw [rowsXor_zero, rowsXor_zero, rowsXor_zero, Nat.zero_xor]
  | m + 1, x, y => by
    rw [rowsXor_succ, rowsXor_succ, rowsXor_succ, rowsXor_xor r m x y, Nat.testBit_xor]
    cases x.testBit m <;> cases y.testBit m <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem lanes_TP7850 : ∀ i < 6, ∀ j < 11,
    laneP (TP7850.getD i 0) j = letterRow (letters.getD i 0) j := by decide +kernel

theorem actP_TP7850 {i : Nat} (hi : i < 6) (c : Nat) :
    actP (TP7850.getD i 0) c = act (letters.getD i 0) c := by
  rw [actP_eq_rowsXor, act]
  exact rowsXor_congr (lanes_TP7850 i hi) c

theorem actP_lt (T c : Nat) : actP T c < 2048 := by
  rw [actP_eq_rowsXor]
  exact rowsXor_lt (fun j _ => Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)) le_rfl c

theorem actP_xor (T x y : Nat) : actP T (x ^^^ y) = actP T x ^^^ actP T y := by
  rw [actP_eq_rowsXor, actP_eq_rowsXor, actP_eq_rowsXor, rowsXor_xor]

@[expose] noncomputable def wElt (wd : List Nat) : J := (wd.map fun i => XJ (letters.getD i 0)).prod

theorem letters_getD_mem {i : Nat} (hi : i < 6) : letters.getD i 0 ∈ letters := by
  rw [List.getD_eq_getElem _ _ (by simpa [letters] using hi)]
  exact List.getElem_mem _

theorem wElt_mem {wd : List Nat} (hwd : ∀ i ∈ wd, i < 6) : wElt wd ∈ Hj := by
  unfold wElt
  refine Subgroup.list_prod_mem Hj ?_
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact XJ_mem (letters_getD_mem (hwd i hi))

theorem wimgP_eq_foldr : ∀ (wd : List Nat), (∀ i ∈ wd, i < 6) → ∀ c,
    wimgP TP7850 wd c = wd.foldr (fun i => act (letters.getD i 0)) c
  | [], _, _ => rfl
  | i :: wd, hwd, c => by
    rw [wimgP_cons, List.foldr_cons, actP_TP7850 (hwd i List.mem_cons_self),
      wimgP_eq_foldr wd (fun i' hi' => hwd i' (List.mem_cons_of_mem _ hi')) c]

theorem wimgP_lt : ∀ (wd : List Nat) {c : Nat}, c < 2048 → wimgP TP7850 wd c < 2048
  | [], _, hc => hc
  | i :: wd, c, _ => by
    rw [wimgP_cons]
    exact actP_lt _ _

theorem wimgP_zero : ∀ wd : List Nat, wimgP TP7850 wd 0 = 0
  | [] => rfl
  | i :: wd => by
    rw [wimgP_cons, wimgP_zero wd]
    rfl

theorem wimgP_xor : ∀ (wd : List Nat) (x y : Nat),
    wimgP TP7850 wd (x ^^^ y) = wimgP TP7850 wd x ^^^ wimgP TP7850 wd y
  | [], _, _ => rfl
  | i :: wd, x, y => by
    rw [wimgP_cons, wimgP_cons, wimgP_cons, wimgP_xor wd x y, actP_xor]

theorem conj_wElt (hM : MatFacts) {wd : List Nat}
    (hwd : ∀ i ∈ wd, i < 6) (c : Nat) :
    wElt wd * eta uJ 11 c * (wElt wd)⁻¹ = eta uJ 11 (wimgP TP7850 wd c) := by
  rw [wimgP_eq_foldr wd hwd c]
  exact word_conj (fun i => XJ (letters.getD i 0)) (fun i => act (letters.getD i 0)) wd
    (fun i hi c => hX_all hM (letters_getD_mem (hwd i hi)) c) c

theorem mem_spanL_map {f : Nat → Nat} (h0 : f 0 = 0) (hx : ∀ x y, f (x ^^^ y) = f x ^^^ f y) :
    ∀ (B : List Nat) (x : Nat), x ∈ spanL (B.map f) ↔ ∃ d ∈ spanL B, x = f d
  | [], x => by
    rw [List.map_nil, mem_spanL_nil]
    constructor
    · rintro rfl
      exact ⟨0, (mem_spanL_nil 0).mpr rfl, h0.symm⟩
    · rintro ⟨d, hd, rfl⟩
      rw [(mem_spanL_nil d).mp hd, h0]
  | b :: B, x => by
    rw [List.map_cons, mem_spanL_cons, mem_spanL_map h0 hx B, mem_spanL_map h0 hx B]
    constructor
    · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, e⟩)
      · exact ⟨d, (mem_spanL_cons b B d).mpr (Or.inl hd), rfl⟩
      · refine ⟨d ^^^ b, (mem_spanL_cons b B _).mpr (Or.inr ?_), ?_⟩
        · rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        · rw [hx, ← e, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · rintro ⟨d, hd, rfl⟩
      rcases (mem_spanL_cons b B d).mp hd with hd | hd
      · exact Or.inl ⟨d, hd, rfl⟩
      · exact Or.inr ⟨d ^^^ b, hd, by rw [hx]⟩

theorem y8Lk_sub_span : allL y8Lk (fun c => memK c (spanL y8Bk)) = true := by decide +kernel

theorem span_sub_y8Lk : allL (spanL y8Bk) (fun c => memK c y8Lk) = true := by decide +kernel

theorem y8Lk_lt : allL y8Lk (fun c => Nat.blt c 2048) = true := by decide +kernel

theorem mem_y8Lk_iff (c : Nat) : c ∈ y8Lk ↔ c ∈ spanL y8Bk :=
  ⟨fun h => memK_iff.mp (allL_iff.mp y8Lk_sub_span c h),
    fun h => memK_iff.mp (allL_iff.mp span_sub_y8Lk c h)⟩

theorem lt_of_mem_y8Lk {c : Nat} (h : c ∈ y8Lk) : c < 2048 := by
  have := allL_iff.mp y8Lk_lt c h
  rwa [Nat.blt_eq] at this

theorem mem_conjMasks_iff (hM : MatFacts) {Y : Subgroup J}
    (hY : ∀ g, g ∈ Y ↔ ∃ d < 2048, g = eta uJ 11 d ∧ d ∈ y8Lk) {wd : List Nat}
    (hwd : ∀ i ∈ wd, i < 6) (c : Nat) :
    c ∈ spanL (imgP TP7850 wd y8Bk) ↔
      c < 2048 ∧ (wElt wd)⁻¹ * eta uJ 11 c * wElt wd ∈ Y := by
  rw [imgP_eq, mem_spanL_map (wimgP_zero wd) (wimgP_xor wd)]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd' := (mem_y8Lk_iff d).mpr hd
    have hdl := lt_of_mem_y8Lk hd'
    refine ⟨wimgP_lt wd hdl, ?_⟩
    rw [← conj_wElt hM hwd d]
    have e : (wElt wd)⁻¹ * (wElt wd * eta uJ 11 d * (wElt wd)⁻¹) * wElt wd = eta uJ 11 d := by
      group
    rw [e]
    exact (hY _).mpr ⟨d, hdl, rfl, hd'⟩
  · rintro ⟨hc, hy⟩
    obtain ⟨d, hdl, e, hd⟩ := (hY _).mp hy
    refine ⟨d, (mem_y8Lk_iff d).mp hd, ?_⟩
    have e2 : eta uJ 11 c = eta uJ 11 (wimgP TP7850 wd d) := by
      rw [← conj_wElt hM hwd d, ← e]
      group
    exact CFSG.Quasithin.J4Loc.eta_inj' hM hc (wimgP_lt wd hdl) e2

theorem c7850_card_le_of_cosets {G : Type*} [Group G] [Finite G] {H N : Subgroup G}
    (hNH : N ≤ H) {n : ℕ} (h : Fin n → G) (hh : ∀ i, h i ∈ H)
    (hinj : ∀ i j, (h i)⁻¹ * h j ∈ N → i = j) : n * Nat.card N ≤ Nat.card H := by
  let f : Fin n → ↥H ⧸ N.subgroupOf H := fun i => QuotientGroup.mk ⟨h i, hh i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    have h1 := QuotientGroup.eq.mp hij
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa using h2
  have hn : n ≤ (N.subgroupOf H).index := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_fin] at this
  have hNcard : Nat.card ↥(N.subgroupOf H) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hci := Subgroup.card_mul_index (N.subgroupOf H)
  rw [hNcard] at hci
  rw [← hci, mul_comm]
  exact Nat.mul_le_mul_left _ hn

theorem indK_eq_of_mem {l l' : List Nat} (h : ∀ c, c ∈ l ↔ c ∈ l') : indK l = indK l' :=
  Nat.eq_of_testBit_eq fun c => by
    rw [Bool.eq_iff_iff, indK_testBit, indK_testBit]
    exact h c

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31.J4M4 in
theorem orb_sound (hM : MatFacts)
    (hy8 : ∀ c < 2048, (∀ k < 31, eta uJ 11 c • (gJ • kwRow k) = gJ • kwRow k) ↔ c ∈ y8Lk) :
    759 * Nat.card ↥(Hj ⊓ Subgroup.normalizer ((Eg uJ 11 ⊓
      fixingSubgroup J {v : Row | ∃ k < 31, v = gJ • kwRow k} : Subgroup J) : Set J)) ≤ Nat.card ↥Hj := by
  generalize hYdef : (Eg uJ 11 ⊓
      fixingSubgroup J {v : Row | ∃ k < 31, v = gJ • kwRow k} : Subgroup J) = Y
  have hY : ∀ g, g ∈ Y ↔ ∃ d < 2048, g = eta uJ 11 d ∧ d ∈ y8Lk := by
    intro g
    rw [← hYdef, Subgroup.mem_inf, mem_fixingSubgroup_iff]
    constructor
    · rintro ⟨hE, hF⟩
      obtain ⟨d, hd, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hE
      refine ⟨d, hd, rfl, (hy8 d hd).mp fun k hk => hF _ ⟨k, hk, rfl⟩⟩
    · rintro ⟨d, hd, rfl, hm⟩
      refine ⟨eta_mem_Eg 11 le_rfl d, ?_⟩
      rintro _ ⟨k, hk, rfl⟩
      exact (hy8 d hd).mpr hm k hk
  have hO := c7850_orb
  have hL := c7850_orbLen
  generalize w = W at hO hL
  obtain ⟨hlet, hkeys⟩ := orbK_spec hO
  have hlen : W.length = 759 := beq_iff.mp hL
  have hnd : (W.map (orbKey TP7850 y8Bk)).Nodup := hkeys.imp ne_of_lt
  let wd : Fin 759 → List Nat := fun i => W[i.1]'(by rw [hlen]; exact i.2)
  have hwd : ∀ i, ∀ l ∈ wd i, l < 6 := fun i => hlet _ (List.getElem_mem _)
  refine c7850_card_le_of_cosets inf_le_left (fun i => wElt (wd i)) (fun i => wElt_mem (hwd i)) ?_
  intro i j hij
  have hn : (wElt (wd i))⁻¹ * wElt (wd j) ∈ Subgroup.normalizer (Y : Set J) := hij.2
  generalize ha : wElt (wd i) = a at hn
  generalize hb : wElt (wd j) = b at hn
  have key : ∀ y, y ∈ Y ↔ (a⁻¹ * b)⁻¹ * y * (a⁻¹ * b) ∈ Y := by
    intro y
    have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) y
    rwa [inv_inv] at this
  have hmem : ∀ c, c ∈ spanL (imgP TP7850 (wd i) y8Bk) ↔ c ∈ spanL (imgP TP7850 (wd j) y8Bk) := by
    intro c
    rw [mem_conjMasks_iff hM hY (hwd i) c, mem_conjMasks_iff hM hY (hwd j) c, ha, hb,
      key (a⁻¹ * eta uJ 11 c * a)]
    have e : (a⁻¹ * b)⁻¹ * (a⁻¹ * eta uJ 11 c * a) * (a⁻¹ * b) = b⁻¹ * eta uJ 11 c * b := by
      group
    rw [e]
  have hk : orbKey TP7850 y8Bk (wd i) = orbKey TP7850 y8Bk (wd j) := indK_eq_of_mem hmem
  have hlen' : (W.map (orbKey TP7850 y8Bk)).length = 759 := by rw [List.length_map, hlen]
  have hgi : (W.map (orbKey TP7850 y8Bk))[i.1]'(by rw [hlen']; exact i.2) =
      orbKey TP7850 y8Bk (wd i) := List.getElem_map _
  have hgj : (W.map (orbKey TP7850 y8Bk))[j.1]'(by rw [hlen']; exact j.2) =
      orbKey TP7850 y8Bk (wd j) := List.getElem_map _
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp (by rw [hgi, hgj, hk]))

end CertificateChecks.KernelJ4NP7850
