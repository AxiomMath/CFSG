module

public import Certificates.Kernel.GL33K.Members
public import Certificates.Kernel.GL33K.Orbits
public import Certificates.Kernel.GL33K.Rest
public import CFSG.Certificates.Kernel.GL33KSound
public import CFSG.Certificates.Kernel.GL33KFacts
import Mathlib.Algebra.Field.ZMod
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KD.GL33K

open CFSG.KC.GL33K CFSG.GL33 Subgroup
open scoped Matrix

noncomputable abbrev memG (i : ℕ) : Subgroup G := sub2 (gA i) (gB i)

theorem memC_all : ∀ i < 13, memC i = true := by
  intro i hi
  interval_cases i
  exacts [ch1255001m_0, ch1255001m_1, ch1255001m_2, ch1255001m_3, ch1255001m_4, ch1255001m_5,
    ch1255001m_6, ch1255001m_7, ch1255001m_8, ch1255001m_9, ch1255001m_10, ch1255001m_11,
    ch1255001m_12]

theorem orbC_all : ∀ i < 13, orbC i = true := by
  intro i hi
  interval_cases i
  exacts [ch1255001o_0, ch1255001o_1, ch1255001o_2, ch1255001o_3, ch1255001o_4, ch1255001o_5,
    ch1255001o_6, ch1255001o_7, ch1255001o_8, ch1255001o_9, ch1255001o_10, ch1255001o_11,
    ch1255001o_12]

theorem normC_all : ∀ i < 13, normC i = true := by
  intro i hi
  interval_cases i
  exacts [ch1255001n_0, ch1255001n_1, ch1255001n_2, ch1255001n_3, ch1255001n_4, ch1255001n_5,
    ch1255001n_6, ch1255001n_7, ch1255001n_8, ch1255001n_9, ch1255001n_10, ch1255001n_11,
    ch1255001n_12]

theorem caseC_all : ∀ i < 13, caseC i = true := by
  intro i hi
  interval_cases i
  exacts [ch1255001c_0, ch1255001c_1, ch1255001c_2, ch1255001c_3, ch1255001c_4, ch1255001c_5,
    ch1255001c_6, ch1255001c_7, ch1255001c_8, ch1255001c_9, ch1255001c_10, ch1255001c_11,
    ch1255001c_12]

theorem good_of_detC {c : ℕ} (h : CFSG.GL33.Native.detC c ≠ 0) : Good c := by
  unfold Good
  rw [det_toM]
  intro h0
  have h1 := congrArg ZMod.val h0
  rw [ZMod.val_natCast, ZMod.val_zero] at h1
  have hlt : CFSG.GL33.Native.detC c < 3 := by
    unfold CFSG.GL33.Native.detC
    exact Nat.mod_lt _ (by norm_num)
  rw [Nat.mod_eq_of_lt hlt] at h1
  exact h h1

theorem good_of_mem {c : ℕ} (hc : c ∈ goodL) : Good c := by
  have h := ch1255001good0
  rw [goodC, allK_iff] at h
  have h1 : (CFSG.GL33.Native.detC c != 0) = true := h c hc
  rw [bne_iff_ne] at h1
  exact good_of_detC h1

theorem getD_mem' {α : Type} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem g_length : g.length = 13 := by decide +kernel

theorem ns_length : ns.length = 13 := by decide +kernel

theorem monI_length : 2 ≤ monI.length := by decide +kernel

theorem good_gA {i : ℕ} (hi : i < 13) : Good (gA i) := by
  have h : gA i ∈ g.map (·.1) := List.mem_map_of_mem (getD_mem' _ (by rw [g_length]; exact hi))
  exact good_of_mem (by simp only [goodL, List.mem_append, h, true_or])

theorem good_gB {i : ℕ} (hi : i < 13) : Good (gB i) := by
  have h : gB i ∈ g.map (·.2) := List.mem_map_of_mem (getD_mem' _ (by rw [g_length]; exact hi))
  exact good_of_mem (by simp only [goodL, List.mem_append, h, true_or, or_true])

theorem good_nP {i : ℕ} (hi : i < 13) :
    Good (nP i).1.1 ∧ Good (nP i).1.2 ∧ Good (nP i).2.1 ∧ Good (nP i).2.2 := by
  have hm : nP i ∈ ns := getD_mem' _ (by rw [ns_length]; exact hi)
  have h1 : (nP i).1.1 ∈ ns.map (·.1.1) := List.mem_map_of_mem hm
  have h2 : (nP i).1.2 ∈ ns.map (·.1.2) := List.mem_map_of_mem hm
  have h3 : (nP i).2.1 ∈ ns.map (·.2.1) := List.mem_map_of_mem hm
  have h4 : (nP i).2.2 ∈ ns.map (·.2.2) := List.mem_map_of_mem hm
  refine ⟨good_of_mem ?_, good_of_mem ?_, good_of_mem ?_, good_of_mem ?_⟩ <;>
    simp only [goodL, List.mem_append, h1, h2, h3, h4, true_or, or_true]

theorem good_case {i : ℕ} (hi : i < 13) {c : ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)}
    (hc : c ∈ cs i) : Good c.1 ∧ Good c.2.2.1 ∧ Good c.2.2.2.1 := by
  have hf : ∀ k ∈ [c.1, c.2.2.1, c.2.2.2.1], k ∈ (List.range 13).flatMap (fun i => (cs i).flatMap
      fun c => [c.1, c.2.2.1, c.2.2.2.1]) := fun k hk =>
    List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨c, hc, hk⟩⟩
  have h1 := hf c.1 (by simp)
  have h2 := hf c.2.2.1 (by simp)
  have h3 := hf c.2.2.2.1 (by simp)
  refine ⟨good_of_mem ?_, good_of_mem ?_, good_of_mem ?_⟩ <;>
    simp only [goodL, List.mem_append, h1, h2, h3, true_or, or_true]

theorem good_extra :
    Good monG.1 ∧ Good monG.2 ∧ Good sylG.1 ∧ Good sylG.2 ∧ Good u13 ∧ Good m1 ∧ Good sl1i ∧
      Good sl2i := by
  have h : ∀ k ∈ [monG.1, monG.2, sylG.1, sylG.2, u13, m1, sl1i, sl2i], Good k := fun k hk =>
    good_of_mem (by simp only [goodL, List.mem_append, hk, true_or, or_true])
  exact ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp),
    h _ (by simp), h _ (by simp), h _ (by simp)⟩

theorem good_monI {k : ℕ} (hk : k ∈ monI) : Good k :=
  good_of_mem (by simp only [goodL, List.mem_append, hk, true_or, or_true])

theorem good_v4 {k : ℕ} (hk : k ∈ v4) : Good k :=
  good_of_mem (by simp only [goodL, List.mem_append, hk, true_or, or_true])

theorem good_v4O {r : ℕ × ℕ} (hr : r ∈ v4O) : Good r.1 ∧ Good r.2 := by
  have h1 : r.1 ∈ v4O.map (·.1) := List.mem_map_of_mem hr
  have h2 : r.2 ∈ v4O.map (·.2) := List.mem_map_of_mem hr
  exact ⟨good_of_mem (by simp only [goodL, List.mem_append, h1, true_or, or_true]),
    good_of_mem (by simp only [goodL, List.mem_append, h2, or_true])⟩

theorem encode_ofCode {c : ℕ} (hc : c < 3 ^ 9) (hg : Good c) :
    encode ((ofCode c : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = c :=
  ofCode_injOn (encode_mem_glCodes _) ((mem_glCodes_iff c).2 ⟨hc, hg⟩) (ofCode_encode _)

theorem eq_of_ofCode_eq {a b : ℕ} (ha : a < 3 ^ 9) (hga : Good a) (hb : b < 3 ^ 9)
    (hgb : Good b) (h : ofCode a = ofCode b) : a = b :=
  ofCode_injOn ((mem_glCodes_iff a).2 ⟨ha, hga⟩) ((mem_glCodes_iff b).2 ⟨hb, hgb⟩) h

theorem good_encode (x : G) : Good (encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) :=
  good_of_mem_glCodes (encode_mem_glCodes x)

theorem ofCode_conjK' {n n' y : ℕ} (hn : Good n) (hn' : Good n') (hy : Good y) :
    ofCode (conjK n n' y) = ofCode n * ofCode y * ofCode n' := by
  unfold conjK
  rw [ofCode_mulK (good_mulK hn hy) hn', ofCode_mulK hn hy]

theorem conjK_lt (n n' y : ℕ) : conjK n n' y < 3 ^ 9 := mulK_lt _ _

theorem oneK_lt : oneK < 3 ^ 9 := by decide

theorem code_of_mem {a b n M : ℕ} {R : List (ℕ × ℕ × ℕ)} (h : memK a b n M R = true)
    (ha : Good a) (hb : Good b) {x : G} (hx : x ∈ sub2 a b) :
    encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) = oneK ∨
      encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ R.map (·.1) :=
  memK_bits h _ ((memK_sound h ha hb).2.1 x hx)

theorem mem_of_bit {a b n M : ℕ} {R : List (ℕ × ℕ × ℕ)} (h : memK a b n M R = true)
    (ha : Good a) (hb : Good b) {c : ℕ} (hc : bitK M c = true) :
    c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ sub2 a b :=
  (memK_sound h ha hb).1 c hc

theorem memK_i {i : ℕ} (hi : i < 13) :
    memK (gA i) (gB i) (ords.getD i 0) (mM i) (mR i) = true := by
  have h := memC_all i hi
  rw [memC] at h
  exact h

theorem card_memG {i : ℕ} (hi : i < 13) : Nat.card (memG i) = ords.getD i 0 :=
  (memK_sound (memK_i hi) (good_gA hi) (good_gB hi)).2.2

theorem bit_memG {i : ℕ} (hi : i < 13) {c : ℕ} (hc : bitK (mM i) c = true) :
    c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ memG i :=
  mem_of_bit (memK_i hi) (good_gA hi) (good_gB hi) hc

theorem mem_normalizer_of_bits {a b n M : ℕ} {R : List (ℕ × ℕ × ℕ)} (h : memK a b n M R = true)
    (ha : Good a) (hb : Good b) {p p' : ℕ} (hp : Good p) (hp' : Good p')
    (hpp : mulK p p' = oneK) (h1 : bitK M (conjK p p' a) = true)
    (h2 : bitK M (conjK p p' b) = true) : ofCode p ∈ normalizer (sub2 a b : Set G) := by
  apply mem_normalizer_of_conj
  rintro k (rfl | rfl)
  · have := (mem_of_bit h ha hb h1).2.2
    rwa [ofCode_conjK hp hp' ha hpp] at this
  · have := (mem_of_bit h ha hb h2).2.2
    rwa [ofCode_conjK hp hp' hb hpp] at this

theorem normC_parts {i : ℕ} (hi : i < 13) :
    mulK (nP i).1.1 (nP i).1.2 = oneK ∧ mulK (nP i).2.1 (nP i).2.2 = oneK ∧
      bitK (mM i) (conjK (nP i).1.1 (nP i).1.2 (gA i)) = true ∧
      bitK (mM i) (conjK (nP i).1.1 (nP i).1.2 (gB i)) = true ∧
      bitK (mM i) (conjK (nP i).2.1 (nP i).2.2 (gA i)) = true ∧
      bitK (mM i) (conjK (nP i).2.1 (nP i).2.2 (gB i)) = true := by
  have h := normC_all i hi
  rw [normC] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem normGens_le' {i : ℕ} (hi : i < 13) :
    sub2 (nP i).1.1 (nP i).2.1 ≤ normalizer (memG i : Set G) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := normC_parts hi
  obtain ⟨g1, g2, g3, g4⟩ := good_nP hi
  exact closure_le_of_gens
    (mem_normalizer_of_bits (memK_i hi) (good_gA hi) (good_gB hi) g1 g2 h1 h3 h4)
    (mem_normalizer_of_bits (memK_i hi) (good_gA hi) (good_gB hi) g3 g4 h2 h5 h6)

theorem orb_i {i : ℕ} (hi : i < 13) :
    orbK (nP i).1.1 (nP i).1.2 (nP i).2.1 (nP i).2.2 (mM i) ((cs i).map (·.1)) T (oR i) 0 =
      true := by
  have h := orbC_all i hi
  rw [orbC] at h
  exact h

theorem case_spec' {i : ℕ} (hi : i < 13) {c : ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)}
    (hc : c ∈ cs i) : c.2.1 < 13 ∧ memG i ⊔ zpowers (ofCode c.1) =
      (memG c.2.1).map (MulAut.conj (ofCode c.2.2.1)⁻¹).toMonoidHom := by
  have hall := caseC_all i hi
  rw [caseC, allK_iff] at hall
  have h := hall c hc
  obtain ⟨gx, gh, gh'⟩ := good_case hi hc
  obtain ⟨x, j, p, p', w1, w2⟩ := c
  rw [caseOne] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hj, hpp⟩, b1⟩, b2⟩, b3⟩, e1⟩, e2⟩ := h
  simp only at gx gh gh' ⊢
  have ha := good_gA hi
  have hb := good_gB hi
  have hinv : ofCode p' = (ofCode p)⁻¹ := ofCode_inv_of_mulK gh gh' hpp
  refine ⟨hj, le_antisymm ?_ ?_⟩
  · have key : ∀ k : ℕ, Good k → bitK (mM j) (conjK p p' k) = true →
        ofCode k ∈ (memG j).map (MulAut.conj (ofCode p)⁻¹).toMonoidHom := by
      intro k hk hbit
      have hm := (bit_memG hj hbit).2.2
      rw [ofCode_conjK gh gh' hk hpp] at hm
      exact ⟨_, hm, by simp [mul_assoc]⟩
    refine sup_le (closure_le_of_gens (key _ ha b1) (key _ hb b2)) ?_
    rw [Subgroup.zpowers_le]
    exact key _ gx b3
  · set K := memG i ⊔ zpowers (ofCode x)
    have haK : ofCode (gA i) ∈ K := (le_sup_left : memG i ≤ K) (Subgroup.subset_closure (by simp))
    have hbK : ofCode (gB i) ∈ K := (le_sup_left : memG i ≤ K) (Subgroup.subset_closure (by simp))
    have hxK : ofCode x ∈ K := (le_sup_right : zpowers (ofCode x) ≤ K) (Subgroup.mem_zpowers _)
    have hconj : ∀ y : ℕ, Good y → ofCode (conjK p' p y) =
        (MulAut.conj (ofCode p)⁻¹).toMonoidHom (ofCode y) := by
      intro y hy
      rw [ofCode_conjK' gh' gh hy, hinv]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    rw [memG, sub2, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · rw [← hconj _ (good_gA hj), ← e1]
      exact (evalK_mem ha hb gx haK hbK hxK w1).2
    · rw [← hconj _ (good_gB hj), ← e2]
      exact (evalK_mem ha hb gx haK hbK hxK w2).2

def tSet : Set G := {x | bitK TM (encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) = true}

theorem tC_parts :
    setK TM T 0 = true ∧ mulK (gA 12) sl1i = oneK ∧ mulK (gB 12) sl2i = oneK ∧
      (∀ t ∈ T, bitK TM (conjK (gA 12) sl1i t) = true ∧ bitK TM (conjK sl1i (gA 12) t) = true ∧
        bitK TM (conjK (gB 12) sl2i t) = true ∧ bitK TM (conjK sl2i (gB 12) t) = true) ∧
      ∀ r ∈ mR 8, bitK TM r.1 = true := by
  have h := ch1255001t0
  rw [tC] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [allK_iff] at h4 h5
  refine ⟨h1, h2, h3, fun t ht => ?_, h5⟩
  have := h4 t ht
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem mem_tSet_iff (x : G) : x ∈ tSet ↔ encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ T :=
  setK_sound tC_parts.1 _

theorem tSet_conj {n n' : ℕ} (hn : Good n) (hn' : Good n')
    (h : ∀ t ∈ T, bitK TM (conjK n n' t) = true) {x : G} (hx : x ∈ tSet) :
    ofCode n * x * ofCode n' ∈ tSet := by
  have ht : Good (encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) := good_encode x
  have hb := h _ ((mem_tSet_iff x).1 hx)
  have e : ofCode (conjK n n' (encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3)))) =
      ofCode n * x * ofCode n' := by
    rw [ofCode_conjK' hn hn' ht, ofCode_encode]
  change bitK TM (encode ((ofCode n * x * ofCode n' : G) : Matrix (Fin 3) (Fin 3) (ZMod 3))) = true
  rw [← e, encode_ofCode (conjK_lt _ _ _) (good_conjK hn hn' ht)]
  exact hb

theorem tSet_conj_memG12 {s : G} (hs : s ∈ memG 12) {x : G} (hx : x ∈ tSet) :
    s * x * s⁻¹ ∈ tSet := by
  obtain ⟨h1, h2, h3, h4, -⟩ := tC_parts
  have ga := good_gA (i := 12) (by norm_num)
  have gb := good_gB (i := 12) (by norm_num)
  obtain ⟨-, -, -, -, -, -, g1, g2⟩ := good_extra
  have ia : ofCode sl1i = (ofCode (gA 12))⁻¹ := ofCode_inv_of_mulK ga g1 h2
  have ib : ofCode sl2i = (ofCode (gB 12))⁻¹ := ofCode_inv_of_mulK gb g2 h3
  have hs' : s ∈ Subgroup.closure ({ofCode (gA 12), ofCode (gB 12)} : Set G) := hs
  clear hs
  revert x
  induction hs' using Subgroup.closure_induction'' with
  | mem s hs =>
    rcases hs with rfl | rfl
    · intro x hx
      have := tSet_conj ga g1 (fun t ht => (h4 t ht).1) hx
      rwa [ia] at this
    · intro x hx
      have := tSet_conj gb g2 (fun t ht => (h4 t ht).2.2.1) hx
      rwa [ib] at this
  | inv_mem s hs =>
    rcases hs with rfl | rfl
    · intro x hx
      have := tSet_conj g1 ga (fun t ht => (h4 t ht).2.1) hx
      simpa only [ia, inv_inv] using this
    · intro x hx
      have := tSet_conj g2 gb (fun t ht => (h4 t ht).2.2.2) hx
      simpa only [ib, inv_inv] using this
  | one =>
    intro x hx
    simpa using hx
  | mul s u _ _ ihs ihu =>
    intro x hx
    have := ihs (ihu hx)
    rwa [show s * (u * x * u⁻¹) * s⁻¹ = s * u * x * (s * u)⁻¹ by group] at this

private theorem card_SL33' : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
  rw [Matrix.card_SL_field (n := 3) (𝔽 := ZMod 3), ZMod.card, Fin.prod_univ_three]
  norm_num

theorem kindC_parts :
    kind = [0, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5] ∧ gA 0 = oneK ∧ gB 0 = oneK ∧
      (∀ j ∈ [1, 2, 3, 4, 5, 7, 8, 11], vecOK j (vec.getD j 0) = true) ∧
      covOK (vec.getD 10 0) = true ∧ CFSG.GL33.Native.detC (gA 12) = 1 ∧
      CFSG.GL33.Native.detC (gB 12) = 1 := by
  have h := ch1255001kind0
  rw [kindC] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  rw [allK_iff] at h4
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem memG12_eq : memG 12 = (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) →* G).range := by
  obtain ⟨-, -, -, -, -, d1, d2⟩ := kindC_parts
  have ga := good_gA (i := 12) (by norm_num)
  have gb := good_gB (i := 12) (by norm_num)
  have hmemR : ∀ a, Good a → CFSG.GL33.Native.detC a = 1 → ofCode a ∈
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) →* G).range := by
    intro a ga' hd
    refine ⟨⟨toM a, by rw [det_toM, hd]; rfl⟩, ?_⟩
    apply Units.ext
    rw [coe_ofCode ga']
    rfl
  have hle : memG 12 ≤ _ := closure_le_of_gens (hmemR _ ga d1) (hmemR _ gb d2)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr (MonoidHom.ofInjective
    (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 3) (R := ZMod 3))).symm.toEquiv,
    card_SL33', card_memG (by norm_num)]
  decide

private theorem minusOne_comm'' (x : G) :
    x * ofCode CFSG.GL33.Native.minusOneC = ofCode CFSG.GL33.Native.minusOneC * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_ofCode good_minusOneC, toM_minusOneC, mul_neg_one,
    neg_one_mul]

theorem exists_memG12_conj (h : G) : ∃ s ∈ memG 12, ∀ x : G, h * x * h⁻¹ = s * x * s⁻¹ := by
  have hdet : ∀ k : G, (k : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 → k ∈ memG 12 := by
    intro k hk
    rw [memG12_eq]
    exact ⟨⟨(k : Matrix (Fin 3) (Fin 3) (ZMod 3)), hk⟩, Units.ext rfl⟩
  have hd0 : (h : Matrix (Fin 3) (Fin 3) (ZMod 3)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  have hcases : ∀ d : ZMod 3, d ≠ 0 → d = 1 ∨ -d = 1 := by decide
  rcases hcases _ hd0 with h1 | h1
  · exact ⟨h, hdet h h1, fun _ => rfl⟩
  · refine ⟨h * ofCode CFSG.GL33.Native.minusOneC, hdet _ ?_, fun x => ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, coe_ofCode good_minusOneC, toM_minusOneC,
        Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
      have hm : ((-1 : ZMod 3) ^ 3 * 1) = -1 := by decide
      rw [hm, mul_neg_one]
      exact h1
    · have hc : ofCode CFSG.GL33.Native.minusOneC * x = x * ofCode CFSG.GL33.Native.minusOneC :=
        (minusOne_comm'' x).symm
      calc h * x * h⁻¹ = h * (x * ofCode CFSG.GL33.Native.minusOneC *
            (ofCode CFSG.GL33.Native.minusOneC)⁻¹) * h⁻¹ := by group
        _ = h * (ofCode CFSG.GL33.Native.minusOneC * x *
            (ofCode CFSG.GL33.Native.minusOneC)⁻¹) * h⁻¹ := by rw [hc]
        _ = h * ofCode CFSG.GL33.Native.minusOneC * x *
            (h * ofCode CFSG.GL33.Native.minusOneC)⁻¹ := by group

theorem three_mem {y : G} {k : ℕ} (hy : orderOf y = 3 ^ k) (hy1 : y ≠ 1) : y ∈ tSet := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h8 : (8 : ℕ) < 13 := by norm_num
  have hP : Nat.card (memG 8) = 27 := by rw [card_memG h8]; decide
  have hPp : IsPGroup 3 (memG 8) := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have hidx : ¬ 3 ∣ (memG 8).index := by
    have := Subgroup.card_mul_index (memG 8)
    rw [hP, card_G] at this
    have h416 : (memG 8).index = 416 := by omega
    rw [h416]
    norm_num
  set S₀ : Sylow 3 G := hPp.toSylow hidx
  have hyp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hy])
  obtain ⟨P, hyP⟩ := hyp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S₀ P
  have hwP : y ∈ ((h • S₀ : Sylow 3 G) : Subgroup G) := by rw [hh]; exact hyP (mem_zpowers y)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hwP
  have hp : h⁻¹ * y * h ∈ memG 8 := hwP
  have hp1 : h⁻¹ * y * h ≠ 1 := by
    intro e
    apply hy1
    have : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
    rw [this, e]
    group
  have hpT : h⁻¹ * y * h ∈ tSet := by
    rcases code_of_mem (memK_i h8) (good_gA h8) (good_gB h8) hp with e | e
    · exfalso
      apply hp1
      rw [← ofCode_encode (h⁻¹ * y * h), e, ofCode_oneK]
    · obtain ⟨r, hr, er⟩ := List.mem_map.1 e
      change bitK TM _ = true
      rw [← er]
      exact tC_parts.2.2.2.2 r hr
  obtain ⟨s, hs, hsc⟩ := exists_memG12_conj h
  have := tSet_conj_memG12 hs hpT
  rwa [← hsc, show h * (h⁻¹ * y * h) * h⁻¹ = y by group] at this

theorem exists_rep' {i : ℕ} (hi : i < 13) {y : G} {k : ℕ} (hy : orderOf y = 3 ^ k)
    (hy1 : y ≠ 1) : y ∈ memG i ∨ ∃ c ∈ cs i, ∃ n ∈ normalizer (memG i : Set G),
      y = n * ofCode c.1 * n⁻¹ := by
  have htT : encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ T :=
    (mem_tSet_iff y).1 (three_mem hy hy1)
  obtain ⟨g1, g2, g3, g4⟩ := good_nP hi
  obtain ⟨i1, i2, -⟩ := normC_parts hi
  have hX : ∀ x ∈ (cs i).map (·.1), Good x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact (good_case hi hc).1
  rcases orbK_sound (orb_i hi) g1 g2 g3 g4 i1 i2 hX htT with hm | ⟨x, hx, n, hn, e⟩
  · left
    have := (bit_memG hi hm).2.2
    rwa [ofCode_encode] at this
  · right
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    refine ⟨c, hc, n, normGens_le' hi hn, ?_⟩
    rw [ofCode_encode] at e
    exact e

theorem mem_fam_conj {K : Subgroup G} (hK : K ∈ fam memG) (g : G) :
    K.map (MulAut.conj g).toMonoidHom ∈ fam memG := by
  obtain ⟨j, hj, g', rfl⟩ := hK
  exact ⟨j, hj, g * g', map_conj_map_conj _ g g'⟩

theorem memG_mem_fam {j : ℕ} (hj : j < 13) : memG j ∈ fam memG :=
  ⟨j, hj, 1, (map_conj_one _).symm⟩

theorem join_closed' :
    ∀ K ∈ fam memG, ∀ σ : G, (∃ k, orderOf σ = 3 ^ k) → K ⊔ zpowers σ ∈ fam memG := by
  rintro K ⟨j, hj, g, rfl⟩ σ ⟨k, hk⟩
  obtain ⟨y, hσ⟩ : ∃ y, MulAut.conj g y = σ := ⟨_, conj_conj_inv_apply g σ⟩
  have hyk : orderOf y = 3 ^ k := by rw [← hk, ← hσ, MulEquiv.orderOf_eq]
  have hsup : (memG j).map (MulAut.conj g).toMonoidHom ⊔ zpowers σ =
      (memG j ⊔ zpowers y).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hσ]
  rw [hsup]
  refine mem_fam_conj ?_ g
  by_cases hy1 : y = 1
  · rw [hy1, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    exact memG_mem_fam hj
  rcases exists_rep' hj hyk hy1 with hmem | ⟨c, hc, n, hn, e⟩
  · rw [sup_eq_left.2 ((Subgroup.zpowers_le).2 hmem)]
    exact memG_mem_fam hj
  · obtain ⟨hjr, hcase⟩ := case_spec' hj hc
    have : memG j ⊔ zpowers y =
        (memG j ⊔ zpowers (ofCode c.1)).map (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hn, MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← e]
    rw [this, hcase]
    exact mem_fam_conj (mem_fam_conj (memG_mem_fam hjr) _) n

theorem memG_zero : memG 0 = ⊥ := by
  obtain ⟨-, h2, h3, -⟩ := kindC_parts
  rw [memG, sub2, h2, h3, ofCode_oneK, Set.pair_eq_singleton, Subgroup.closure_singleton_one]

theorem memG_ne_bot : ∀ j < 13, j ≠ 0 → memG j ≠ ⊥ := by
  intro j hj hj0 h
  have hc := card_memG hj
  rw [h, Subgroup.card_bot] at hc
  have hpos : 1 < ords.getD j 0 := by interval_cases j <;> first | omega | decide
  omega

theorem kind1' : ∀ j ∈ [1, 2, 3, 4, 5, 7, 8, 11], ∃ v : V, v ≠ 0 ∧ memG j ≤ fixer v := by
  intro j hj
  obtain ⟨-, -, -, h4, -⟩ := kindC_parts
  have hv := h4 j hj
  rw [vecOK] at hv
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at hv
  obtain ⟨⟨⟨h0, hlt⟩, e1⟩, e2⟩ := hv
  have hj13 : j < 13 := by simp at hj; omega
  refine ⟨toV (vec.getD j 0), toV_ne_zero h0 hlt, closure_le_of_gens ?_ ?_⟩
  · change act _ _ = _
    rw [act_ofCode (good_gA hj13), e1]
  · change act _ _ = _
    rw [act_ofCode (good_gB hj13), e2]

theorem kind2' : ∃ f : V, f ≠ 0 ∧ memG 10 ≤ cofixer f := by
  obtain ⟨-, -, -, -, h5, -⟩ := kindC_parts
  rw [covOK] at h5
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h5
  obtain ⟨⟨⟨h0, hlt⟩, e1⟩, e2⟩ := h5
  refine ⟨toV (vec.getD 10 0), toV_ne_zero h0 hlt, closure_le_of_gens ?_ ?_⟩
  · change _ ᵥ* _ = _
    rw [coe_ofCode (good_gA (by norm_num)), ← toV_covC, e1]
  · change _ ᵥ* _ = _
    rw [coe_ofCode (good_gB (by norm_num)), ← toV_covC, e2]

theorem sl' : Nonempty (memG 12 ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) := by
  rw [memG12_eq]
  exact ⟨(MonoidHom.ofInjective
    (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 3) (R := ZMod 3))).symm⟩

private theorem toV_eighteen'' : toV 18 = -toV 9 := by
  funext i
  fin_cases i <;> decide

theorem syl' : ∃ S : Subgroup G, Nat.card S = 16 ∧ ofCode CFSG.GL33.Native.minusOneC ∉ S ∧
    S ≤ lineStab (toV 9) := by
  have h := ch1255001syl0
  rw [sylC] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  obtain ⟨⟨⟨⟨hm, hb⟩, e1⟩, e2⟩, hm1⟩ := h
  obtain ⟨-, -, gs1, gs2, -⟩ := good_extra
  refine ⟨sub2 sylG.1 sylG.2, (memK_sound hm gs1 gs2).2.2, fun hz => ?_,
    closure_le_of_gens ?_ ?_⟩
  · have hz' := (memK_sound hm gs1 gs2).2.1 _ hz
    rw [encode_ofCode (by decide) good_minusOneC] at hz'
    have e : CFSG.GL33.Native.minusOneC = m1 := by rw [hm1]; rfl
    rw [e, hb] at hz'
    exact Bool.false_ne_true hz'
  · change act _ _ = _ ∨ act _ _ = _
    rw [act_ofCode gs1]
    rcases e1 with e | e
    · left; rw [e]
    · right; rw [e, toV_eighteen'']
  · change act _ _ = _ ∨ act _ _ = _
    rw [act_ofCode gs2]
    rcases e2 with e | e
    · left; rw [e]
    · right; rw [e, toV_eighteen'']

theorem powK_lt (a e : ℕ) : powK a (e + 1) < 3 ^ 9 := mulK_lt _ _

theorem c13' : ∃ u ∈ memG 9, orderOf u = 13 ∧
    ∀ n ∈ normalizer (memG 9 : Set G), n * u * n⁻¹ ∈ zpowers u := by
  have h := ch1255001c130
  rw [c13C] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hm, hb⟩, hall⟩ := h
  rw [allK_iff] at hall
  obtain ⟨-, -, -, -, gu, -⟩ := good_extra
  have h9 : (9 : ℕ) < 13 := by norm_num
  have hU : sub2 u13 u13 = zpowers (ofCode u13) := by
    rw [sub2, Set.pair_eq_singleton, ← Subgroup.zpowers_eq_closure]
  have hord : orderOf (ofCode u13) = 13 := by
    rw [← Nat.card_zpowers, ← hU, (memK_sound hm gu gu).2.2]
  refine ⟨ofCode u13, (bit_memG h9 hb).2.2, hord, fun n hn => ?_⟩
  have hyM : n * ofCode u13 * n⁻¹ ∈ memG 9 :=
    (Subgroup.mem_normalizer_iff.1 hn _).1 (bit_memG h9 hb).2.2
  have hy13 : (n * ofCode u13 * n⁻¹) ^ 13 = 1 := by
    rw [conj_pow, ← hord, pow_orderOf_eq_one]
    group
  have he : encode ((n * ofCode u13 * n⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈
      oneK :: (mR 9).map (·.1) := by
    rcases code_of_mem (memK_i h9) (good_gA h9) (good_gB h9) hyM with h1 | h1
    · rw [h1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ h1
  have h1 := hall _ he
  have hp : powK (encode ((n * ofCode u13 * n⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3))) 13 =
      oneK := by
    apply eq_of_ofCode_eq (powK_lt _ _) (good_powK (good_encode _) _) oneK_lt good_oneK
    rw [ofCode_powK (good_encode _), ofCode_oneK, ofCode_encode, hy13]
  change (powK _ 13 != oneK || bitK uM _) = true at h1
  rw [hp, bne_self_eq_false, Bool.false_or] at h1
  have := (mem_of_bit hm gu gu h1).2.2
  rwa [ofCode_encode, hU] at this

theorem conj_three_sub {X : Type*} [Group X] {Vs : Subgroup X} {a b c p q : X}
    (hV : ∀ x ∈ Vs, x = 1 ∨ x = a ∨ x = b ∨ x = c) (hn : p⁻¹ * q ∈ normalizer (Vs : Set X))
    (ha : a ∈ Vs) (hb : b ∈ Vs) (hc : c ∈ Vs) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) :
    ∀ x ∈ ({a, b, c} : Set X), ∃ y ∈ ({a, b, c} : Set X), p * x * p⁻¹ = q * y * q⁻¹ := by
  intro x hx
  obtain ⟨m, hmd⟩ : ∃ m, m = p⁻¹ * q := ⟨_, rfl⟩
  rw [← hmd] at hn
  have hq : q = p * m := by rw [hmd]; group
  subst hq
  have hxV : x ∈ Vs := by rcases hx with rfl | rfl | rfl <;> assumption
  have hx1 : x ≠ 1 := by rcases hx with rfl | rfl | rfl <;> assumption
  have hm : m⁻¹ * x * m ∈ Vs := by
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (Vs : Set X)).inv_mem hn) x).1 hxV
    simpa [mul_assoc] using this
  have hm1 : m⁻¹ * x * m ≠ 1 := by
    intro e
    apply hx1
    have : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
    rw [this, e]
    group
  refine ⟨m⁻¹ * x * m, ?_, ?_⟩
  · rcases hV _ hm with e | e | e | e
    · exact absurd e hm1
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  · group

theorem finset_conj_sub {X : Type*} [Group X] [DecidableEq X] {a b c p q : X}
    (h : ∀ x ∈ ({a, b, c} : Set X), ∃ y ∈ ({a, b, c} : Set X), p * x * p⁻¹ = q * y * q⁻¹) :
    ({p * a * p⁻¹, p * b * p⁻¹, p * c * p⁻¹} : Finset X) ⊆
      {q * a * q⁻¹, q * b * q⁻¹, q * c * q⁻¹} := by
  have key : ∀ x ∈ ({a, b, c} : Set X),
      p * x * p⁻¹ ∈ ({q * a * q⁻¹, q * b * q⁻¹, q * c * q⁻¹} : Finset X) := by
    intro x hx
    obtain ⟨y, hy, e⟩ := h x hx
    rw [e]
    rcases hy with rfl | rfl | rfl <;> simp
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact key a (by simp)
  · exact key b (by simp)
  · exact key c (by simp)

theorem le_index_of_keys {X : Type*} [Group X] [Finite X] {N : Subgroup X} {L : List (ℕ × ℕ)}
    (φ : ℕ × ℕ → X) (key : ℕ × ℕ → ℕ) (hpw : L.Pairwise (fun r s => key r ≠ key s))
    (hk : ∀ r ∈ L, ∀ s ∈ L, (φ r)⁻¹ * φ s ∈ N → key r = key s) : L.length ≤ N.index := by
  classical
  have : Fintype (X ⧸ N) := Fintype.ofFinite _
  have hnd : (L.map fun r => (φ r : X ⧸ N)).Nodup := by
    refine List.pairwise_map.2 (hpw.imp_of_mem fun {r s} hr hs hrs e => hrs ?_)
    exact hk r hr s hs (QuotientGroup.eq.1 e)
  have h1 := hnd.length_le_card
  rw [List.length_map, Fintype.card_eq_nat_card] at h1
  rw [Subgroup.index_eq_card]
  exact h1

theorem a4C_parts :
    v4.length = 3 ∧ memK (v4.getD 0 0) (v4.getD 1 0) 4 vM vR = true ∧
      vM = maskK [oneK, v4.getD 0 0, v4.getD 1 0, v4.getD 2 0] ∧
      bitK (mM 6) (v4.getD 0 0) = true ∧ bitK (mM 6) (v4.getD 1 0) = true ∧
      (∀ c ∈ oneK :: (mR 6).map (·.1), (mulK c c != oneK || bitK vM c) = true) ∧
      memK monG.1 monG.2 48 monM monR = true ∧ (∀ c ∈ oneK :: monR.map (·.1),
        CFSG.GL33.Native.monoC c = true) ∧
      mulK monG.1 (monI.getD 0 0) = oneK ∧ mulK monG.2 (monI.getD 1 0) = oneK ∧
      bitK vM (conjK monG.1 (monI.getD 0 0) (v4.getD 0 0)) = true ∧
      bitK vM (conjK monG.1 (monI.getD 0 0) (v4.getD 1 0)) = true ∧
      bitK vM (conjK monG.2 (monI.getD 1 0) (v4.getD 0 0)) = true ∧
      bitK vM (conjK monG.2 (monI.getD 1 0) (v4.getD 1 0)) = true ∧
      v4O.length = 234 ∧ keysK (v4.getD 0 0) (v4.getD 1 0) (v4.getD 2 0) v4O 0 = true := by
  have h := ch1255001a40
  rw [a4C] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩ := h
  rw [allK_iff] at h6 h8
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem v4_facts : v4.getD 0 0 ≠ v4.getD 1 0 ∧ v4.getD 0 0 ≠ v4.getD 2 0 ∧
    v4.getD 1 0 ≠ v4.getD 2 0 ∧ mulK (v4.getD 0 0) (v4.getD 0 0) = oneK ∧
    mulK (v4.getD 1 0) (v4.getD 1 0) = oneK ∧ mulK (v4.getD 2 0) (v4.getD 2 0) = oneK ∧
    v4.getD 0 0 ≠ oneK ∧ v4.getD 1 0 ≠ oneK ∧ v4.getD 2 0 ≠ oneK := by
  decide +kernel

theorem a4' : ∃ M : Subgroup G, Nat.card M = 48 ∧
    (∀ x ∈ M, ∀ j : Fin 3, ∃ i : Fin 3, act x (Pi.single j 1) ∈
      AddSubgroup.zmultiples (Pi.single i 1 : V)) ∧ normalizer (memG 6 : Set G) ≤ M := by
  obtain ⟨hl, hV, hvM, b1, b2, hinv, hmon, hmono, i1, i2, c1, c2, c3, c4, hlen, hkeys⟩ :=
    a4C_parts
  classical
  obtain ⟨d12, d13, d23, s1, s2, s3, n1, n2, n3⟩ := v4_facts
  set v₁ := v4.getD 0 0
  set v₂ := v4.getD 1 0
  set v₃ := v4.getD 2 0
  have gv : ∀ k < 3, Good (v4.getD k 0) := fun k hk =>
    good_v4 (getD_mem' _ (by rw [hl]; exact hk))
  have g1 := gv 0 (by norm_num)
  have g2 := gv 1 (by norm_num)
  have g3 := gv 2 (by norm_num)
  obtain ⟨gm1, gm2, -⟩ := good_extra
  have gi : ∀ k < 2, Good (monI.getD k 0) := fun k hk =>
    good_monI (getD_mem' _ (by have := monI_length; omega))
  have h6 : (6 : ℕ) < 13 := by norm_num
  set Vs := sub2 v₁ v₂
  set a := ofCode v₁
  set b := ofCode v₂
  set c := ofCode v₃
  have bits : ∀ k, bitK vM k = true ↔ k = oneK ∨ k = v₁ ∨ k = v₂ ∨ k = v₃ := by
    intro k
    rw [hvM, bitK_maskK]
    simp
  have hVel : ∀ x ∈ Vs, x = 1 ∨ x = a ∨ x = b ∨ x = c := by
    intro x hx
    have := (bits _).1 ((memK_sound hV g1 g2).2.1 x hx)
    rw [← ofCode_encode x]
    rcases this with e | e | e | e <;> rw [e]
    · exact Or.inl ofCode_oneK
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hmemV : ∀ k, bitK vM k = true → k < 3 ^ 9 ∧ Good k ∧ ofCode k ∈ Vs :=
    fun k hk => mem_of_bit hV g1 g2 hk
  have l1 := (hmemV v₁ ((bits _).2 (by simp))).1
  have l2 := (hmemV v₂ ((bits _).2 (by simp))).1
  have l3 := (hmemV v₃ ((bits _).2 (by simp))).1
  have ha : a ∈ Vs := (hmemV v₁ ((bits _).2 (by simp))).2.2
  have hb : b ∈ Vs := (hmemV v₂ ((bits _).2 (by simp))).2.2
  have hc : c ∈ Vs := (hmemV v₃ ((bits _).2 (by simp))).2.2
  have hne : ∀ {k k' : ℕ}, k < 3 ^ 9 → Good k → k' < 3 ^ 9 → Good k' → k ≠ k' →
      ofCode k ≠ ofCode k' := fun hk gk hk' gk' hkk e => hkk (eq_of_ofCode_eq hk gk hk' gk' e)
  have hsq : ∀ {k : ℕ}, Good k → mulK k k = oneK → ofCode k * ofCode k = 1 := by
    intro k gk hk
    rw [← ofCode_mulK gk gk, hk, ofCode_oneK]
  have hne1 : ∀ {k : ℕ}, k < 3 ^ 9 → Good k → k ≠ oneK → ofCode k ≠ 1 := by
    intro k hk gk hk1
    rw [← ofCode_oneK]
    exact hne hk gk oneK_lt good_oneK hk1
  have ha1 : a ≠ 1 := hne1 l1 g1 n1
  have hb1 : b ≠ 1 := hne1 l2 g2 n2
  have hc1 : c ≠ 1 := hne1 l3 g3 n3
  have hab : a ≠ b := hne l1 g1 l2 g2 d12
  have hac : a ≠ c := hne l1 g1 l3 g3 d13
  have hbc : b ≠ c := hne l2 g2 l3 g3 d23
  have hVM : Vs ≤ memG 6 := closure_le_of_gens (bit_memG h6 b1).2.2 (bit_memG h6 b2).2.2
  have hsqV : ∀ x ∈ Vs, x * x = 1 := by
    intro x hx
    rcases hVel x hx with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact hsq g1 s1
    · exact hsq g2 s2
    · exact hsq g3 s3
  have hNV : normalizer (memG 6 : Set G) ≤ normalizer (Vs : Set G) := by
    intro n hn
    apply mem_normalizer_of_conj_mem
    intro x hx
    have hyM : n * x * n⁻¹ ∈ memG 6 := (Subgroup.mem_normalizer_iff.1 hn x).1 (hVM hx)
    have hyy : n * x * n⁻¹ * (n * x * n⁻¹) = 1 := by
      rw [show n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ by group, hsqV x hx]
      group
    have he : encode ((n * x * n⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈
        oneK :: (mR 6).map (·.1) := by
      rcases code_of_mem (memK_i h6) (good_gA h6) (good_gB h6) hyM with h1 | h1
      · rw [h1]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h1
    have h1 := hinv _ he
    have hp : mulK (encode ((n * x * n⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)))
        (encode ((n * x * n⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3))) = oneK := by
      apply eq_of_ofCode_eq (mulK_lt _ _) (good_mulK (good_encode _) (good_encode _)) oneK_lt
        good_oneK
      rw [ofCode_mulK (good_encode _) (good_encode _), ofCode_oneK, ofCode_encode, hyy]
    rw [hp, bne_self_eq_false, Bool.false_or] at h1
    have := (hmemV _ h1).2.2
    rwa [ofCode_encode] at this
  set Mon := sub2 monG.1 monG.2
  have gI0 := gi 0 (by norm_num)
  have gI1 := gi 1 (by norm_num)
  have hMonN : Mon ≤ normalizer (Vs : Set G) :=
    closure_le_of_gens (mem_normalizer_of_bits hV g1 g2 gm1 gI0 i1 c1 c2)
      (mem_normalizer_of_bits hV g1 g2 gm2 gI1 i2 c3 c4)
  have hMon48 : Nat.card Mon = 48 := (memK_sound hmon gm1 gm2).2.2
  obtain ⟨hpr, hpw⟩ := keysK_sound hkeys
  set N := normalizer (Vs : Set G)
  have hkey : ∀ r ∈ v4O, keyK v₁ v₂ v₃ r.1 r.2 = ∑ x ∈ ({ofCode r.1 * a * (ofCode r.1)⁻¹,
      ofCode r.1 * b * (ofCode r.1)⁻¹, ofCode r.1 * c * (ofCode r.1)⁻¹} : Finset G),
      2 ^ encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    intro r hr
    classical
    obtain ⟨gr1, gr2⟩ := good_v4O hr
    have ec : ∀ k, Good k → k < 3 ^ 9 → conjK r.1 r.2 k = encode ((ofCode r.1 * ofCode k *
        (ofCode r.1)⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
      intro k gk _
      rw [← ofCode_conjK gr1 gr2 gk (hpr r hr), encode_ofCode (conjK_lt _ _ _)
        (good_conjK gr1 gr2 gk)]
    have inj : ∀ {x y : G}, x ≠ y → ofCode r.1 * x * (ofCode r.1)⁻¹ ≠
        ofCode r.1 * y * (ofCode r.1)⁻¹ := fun hxy e => hxy (by simpa using e)
    rw [Finset.sum_insert (by simp [inj hab, inj hac]), Finset.sum_insert (by simp [inj hbc]),
      Finset.sum_singleton, keyK, ec _ g1 l1, ec _ g2 l2, ec _ g3 l3, add_assoc]
  have hidx : 234 ≤ N.index := by
    rw [← hlen]
    refine le_index_of_keys (fun r => ofCode r.1) (fun r => keyK v₁ v₂ v₃ r.1 r.2) hpw ?_
    intro r hr s hs hm
    have hm' : (ofCode s.1)⁻¹ * ofCode r.1 ∈ N := by
      have := N.inv_mem hm
      simpa using this
    change keyK v₁ v₂ v₃ r.1 r.2 = keyK v₁ v₂ v₃ s.1 s.2
    rw [hkey r hr, hkey s hs]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    exact Finset.Subset.antisymm
      (finset_conj_sub (conj_three_sub hVel hm ha hb hc ha1 hb1 hc1))
      (finset_conj_sub (conj_three_sub hVel hm' ha hb hc ha1 hb1 hc1))
  have hN48 : Nat.card N ≤ 48 := by
    have hprod := Subgroup.card_mul_index N
    rw [card_G] at hprod
    by_contra hlt
    have h2 : 49 * 234 ≤ Nat.card N * N.index := Nat.mul_le_mul (by omega) hidx
    rw [hprod] at h2
    norm_num at h2
  have hMonEq : Mon = N := Subgroup.eq_of_le_of_card_ge hMonN (by rw [hMon48]; exact hN48)
  refine ⟨Mon, hMon48, fun x hx j => ?_, by rw [hMonEq]; exact hNV⟩
  have hcode : encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ oneK :: monR.map (·.1) := by
    rcases code_of_mem hmon gm1 gm2 hx with h1 | h1
    · rw [h1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ h1
  have := act_single_of_monoC (good_encode x) (hmono _ hcode) j
  rwa [ofCode_encode] at this

theorem gfacts : GFacts memG where
  zero := memG_zero
  ne_bot := memG_ne_bot
  join_closed := join_closed'
  kind1 := kind1'
  kind2 := kind2'
  a4 := a4'
  c13 := c13'
  sl := sl'
  syl := syl'

end CFSG.KD.GL33K

end
