module

public import Certificates.Kernel.EaLat318002.Glue
public import Certificates.Kernel.EaLat318002.Slp
public import Certificates.Kernel.EaLat318002.Tags
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Quasithin.H13.LocDblProfDefs
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelEaLat318002

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat
open CFSG.KC.Misc.Clos (pcode ClosEnc pcode_enc pcode_img clos_card)
open CFSG.Blueprint CFSG.Open CFSG.Sporadic.Mathieu CFSG.Quasithin.H13.LocDbl.M24Prof

abbrev Γ24 : Type := ↥NativeSporadic.M24

@[expose] def enc24 (x : Γ24) : ℕ := pcode (x : Perm (Fin 24))

theorem enc24_enc : ClosEnc enc24 (mul 24) (one 24) := by
  have h := pcode_enc (n := 24) (by norm_num)
  exact ⟨h.enc_one, fun a b => h.enc_mul a b, fun a b hab => Subtype.ext (h.inj hab)⟩

theorem slices_s : ∀ k < 30, ch318002s k = true := by
  intro k hk
  interval_cases k
  exacts [ch318002s0, ch318002s1, ch318002s2, ch318002s3, ch318002s4, ch318002s5, ch318002s6,
    ch318002s7, ch318002s8, ch318002s9, ch318002s10, ch318002s11, ch318002s12, ch318002s13,
    ch318002s14, ch318002s15, ch318002s16, ch318002s17, ch318002s18, ch318002s19, ch318002s20,
    ch318002s21, ch318002s22, ch318002s23, ch318002s24, ch318002s25, ch318002s26, ch318002s27,
    ch318002s28, ch318002s29]

theorem slp_all : ∀ s < 590, slpAt s = true := by
  intro s hs
  have h := slices_s (s / 20) (by omega)
  rw [ch318002s, allN_iff] at h
  have h2 := h (s % 20) (Nat.mod_lt _ (by norm_num))
  rw [letB_eq, show Nat.add (Nat.mul 20 (s / 20)) (s % 20) = s by
    change 20 * (s / 20) + s % 20 = s
    omega, impB_iff] at h2
  exact h2 (blt_iff.2 hs)

theorem slp_step (s : ℕ) (h : slpAt s = true) :
    ∃ a b, a < s + 2 ∧ b < s + 2 ∧ NC (s + 2) = mul 24 (NC a) (NC b) := by
  rw [slpAt, slpW, letB_eq, letB_eq, letB_eq] at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  obtain ⟨h3, h4⟩ := andB_iff.1 h2
  exact ⟨_, _, blt_iff.1 h1, blt_iff.1 h3, beq_iff.1 h4⟩

theorem pcode_a : pcode m24gA = 817395973838868159142633316802379971 := by decide +kernel

theorem pcode_b : pcode m24gB = 938078705133617800621527216201835139 := by decide +kernel

theorem nc_ab : NC 0 = 817395973838868159142633316802379971 ∧
    NC 1 = 938078705133617800621527216201835139 := by
  obtain ⟨h1, h2⟩ := andB_iff.1 ch318002s_ab
  exact ⟨beq_iff.1 h1, beq_iff.1 h2⟩

theorem slp_mem : ∀ k < 592, ∃ g ∈ NativeSporadic.M24, pcode g = NC k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k, ih, hk with
    | 0, _, _ => exact ⟨m24gA, m24a.2, by rw [pcode_a, nc_ab.1]⟩
    | 1, _, _ => exact ⟨m24gB, m24b.2, by rw [pcode_b, nc_ab.2]⟩
    | s + 2, ih, hk =>
      obtain ⟨a, b, ha, hb, he⟩ := slp_step s (slp_all s (by omega))
      obtain ⟨x, hx, hxa⟩ := ih a ha (by omega)
      obtain ⟨y, hy, hyb⟩ := ih b hb (by omega)
      refine ⟨x * y, NativeSporadic.M24.mul_mem hx hy, ?_⟩
      rw [he, ← hxa, ← hyb]
      exact (pcode_enc (n := 24) (by norm_num)).enc_mul x y

noncomputable def nd (k : ℕ) : Γ24 :=
  if h : k < 592 then ⟨(slp_mem k h).choose, (slp_mem k h).choose_spec.1⟩ else 1

theorem enc_nd {k : ℕ} (hk : k < 592) : enc24 (nd k) = NC k := by
  unfold nd
  rw [dif_pos hk]
  exact (slp_mem k hk).choose_spec.2

noncomputable def gensR : List Γ24 := [nd 161, nd 303, nd 431, nd 591]

theorem gr_nd : GR 0 = NC 161 ∧ GR 1 = NC 303 ∧ GR 2 = NC 431 ∧ GR 3 = NC 591 := by
  obtain ⟨h0, h⟩ := andB_iff.1 ch318002s_gr
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  exact ⟨beq_iff.1 h0, beq_iff.1 h1, beq_iff.1 h2, beq_iff.1 h3⟩

theorem hG : ∀ j < gensR.length, GR j = enc24 (gensR.getD j 1) := by
  intro j hj
  obtain ⟨h0, h1, h2, h3⟩ := gr_nd
  have hj' : j < 4 := hj
  interval_cases j
  · change GR 0 = enc24 (nd 161)
    rw [h0, enc_nd (by norm_num)]
  · change GR 1 = enc24 (nd 303)
    rw [h1, enc_nd (by norm_num)]
  · change GR 2 = enc24 (nd 431)
    rw [h2, enc_nd (by norm_num)]
  · change GR 3 = enc24 (nd 591)
    rw [h3, enc_nd (by norm_num)]

theorem tgMask_bit (T : ℕ → ℕ) : ∀ m i, (tgMask T m).testBit i = true → ∃ e < m, T e = i := by
  intro m
  induction m with
  | zero =>
    intro i h
    have e0 : tgMask T 0 = 0 := rfl
    rw [e0, Nat.zero_testBit] at h
    exact absurd h (by simp)
  | succ m ih =>
    intro i h
    have e1 : tgMask T (m + 1) = tgMask T m ||| 1 <<< T m := rfl
    rw [e1, Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
    rcases h with h | h
    · obtain ⟨e, he, hTe⟩ := ih i h
      exact ⟨e, by omega, hTe⟩
    · exact ⟨m, by omega, of_decide_eq_true h⟩

theorem tag_cover_of (T : ℕ → ℕ) (h : tgW T = true) : ∀ i < 191, ∃ e < 1024, T e = i := by
  intro i hi
  rw [tgW, letB_eq] at h
  have h2 : tgMask T 1024 &&& (2 ^ 191 - 1) = 2 ^ 191 - 1 := beq_iff.1 h
  have hb : (2 ^ 191 - 1 : ℕ).testBit i = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  rw [← h2, Nat.testBit_and, Bool.and_eq_true] at hb
  exact tgMask_bit T 1024 i hb.1

theorem tag_v : ∀ e < 1024, TG e < 191 → EC e = V (TG e) := by
  intro e he ht
  have h := (list_all e he).2.2.2
  rw [tagAt, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq] at h
  have hb : Nat.blt (TG e) 191 = true := blt_iff.2 ht
  rw [hb] at h
  exact beq_iff.1 h

theorem v_exists : ∀ i < 191, ∃ g : Γ24, enc24 g = V i := by
  intro i hi
  obtain ⟨e, he, hte⟩ := tag_cover_of TG ch318002t i hi
  obtain ⟨g, -, hg⟩ := (clos_card enc24_enc gensR hG (by norm_num)
    (fun k hk => (list_all k hk).1) (fun k hk => (list_all k hk).2.1)).1 e he
  refine ⟨g, ?_⟩
  rw [hg, tag_v e he (hte ▸ hi), hte]

noncomputable def vv (i : ℕ) : Γ24 := if h : i < 191 then (v_exists i h).choose else 1

theorem enc_vv {i : ℕ} (hi : i < 191) : enc24 (vv i) = V i := by
  unfold vv
  rw [dif_pos hi]
  exact (v_exists i hi).choose_spec

theorem hncw : ∀ x y : Γ24, ∀ w < 24, ncw24 (enc24 x) (enc24 y) w = true → x * y ≠ y * x :=
  fun x y w hw h hxy => ncw24_sound x y w hw h (congrArg Subtype.val hxy)

theorem r_ea : Nat.card (Subgroup.closure {g | g ∈ gensR}) = 1024 ∧
    ∀ K : Subgroup Γ24, K ≤ Subgroup.closure {g | g ∈ gensR} →
      (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) → (∀ x ∈ K, x * x = 1) →
      ∃ f < 7507, ∀ x, x ∈ K ↔ x = 1 ∨ ∃ i ∈ recS REC f, vv i = x :=
  ea_of_checks enc24_enc gensR hG (by norm_num) (fun k hk => (list_all k hk).1)
    (fun k hk => (list_all k hk).2.1) (fun k hk => (list_all k hk).2.2.1) (by norm_num)
    (by norm_num) vv (fun i hi => enc_vv hi) hncw wit_prb tag_all uni_all base_ok gen_all cov_all

theorem ent_lt : ∀ f < 7507, ∀ i ∈ recS REC f, i < 191 := by
  have hu := uni_of_checks (by norm_num) enc24_enc vv (fun i hi => enc_vv hi) hncw wit_prb uni_all
  have hr := recs_of_checks (by norm_num) vv hu.2 base_ok gen_all cov_all
  exact fun f hf => (recs_inv hu.1 hr f hf).lt

theorem card_recS (f : ℕ) : (recS REC f).card ≤ recSz REC f :=
  Finset.card_image_le.trans (Finset.card_range _).le

theorem card_le (E : Subgroup Γ24) {S : Finset ℕ}
    (hE : ∀ x, x ∈ E ↔ x = 1 ∨ ∃ i ∈ S, vv i = x) : Nat.card E ≤ S.card + 1 := by
  classical
  have hsub : (E : Set Γ24) ⊆ ↑(aSet vv S) := fun x hx => by
    rw [Finset.mem_coe, mem_aSet]
    exact (hE x).1 hx
  calc Nat.card E = (E : Set Γ24).ncard := Nat.card_coe_set_eq _
    _ ≤ (↑(aSet vv S) : Set Γ24).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (aSet vv S).card := Set.ncard_coe_finset _
    _ ≤ S.card + 1 := by
      unfold aSet
      have := Finset.card_image_le (s := S) (f := vv)
      have := Finset.card_insert_le (1 : Γ24) (S.image vv)
      omega

theorem orbW_testBit (W : ℕ → ℕ) (el sz p q : ℕ) :
    (orbW W el sz p).testBit q = true ↔ p = q ∨ ∃ t < sz, img (W (fld el (8 * t) 255)) p = q := by
  refine (rec_or_testBit (1 <<< p) _ (fun t => 1 <<< img (W (fld el (8 * t) 255)) p)
    (fun t x => rfl) q sz).trans ?_
  simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]

theorem pop24_eq (x : ℕ) : pop24 x = ((Finset.range 24).filter fun i => x.testBit i = true).card := by
  have key : ∀ m, Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc + ((x >>> i) &&& 1)) m =
      ((Finset.range m).filter fun i => x.testBit i = true).card := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      change Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc + ((x >>> i) &&& 1)) m +
        ((x >>> m) &&& 1) = _
      rw [ih, Finset.range_add_one (n := m), Finset.filter_insert]
      have e : (x >>> m) &&& 1 = if x.testBit m = true then 1 else 0 := by
        rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ m) with h | h <;> simp [h]
      rw [e]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
  exact key 24

theorem sum_digits_lt (d : ℕ → ℕ) (hd : ∀ s, d s < 256) :
    ∀ K, ∑ s ∈ Finset.range K, d s * 256 ^ s < 256 ^ K := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h2 : d K * 256 ^ K ≤ 255 * 256 ^ K := Nat.mul_le_mul_right _ (by have := hd K; omega)
    nlinarith

theorem digit_sum (d : ℕ → ℕ) (hd : ∀ s, d s < 256) : ∀ K, ∀ j < K,
    (∑ s ∈ Finset.range K, d s * 256 ^ s) / 256 ^ j % 256 = d j := by
  intro K
  induction K with
  | zero => intro j hj; omega
  | succ K ih =>
    intro j hj
    rw [Finset.sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have hK : (256 : ℕ) ^ K = 256 ^ (K - j - 1) * 256 * 256 ^ j := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      have e : d K * 256 ^ K = d K * 256 ^ (K - j - 1) * 256 * 256 ^ j := by
        rw [hK]
        ring
      rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
      exact ih j hj
    · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (sum_digits_lt d hd j),
        zero_add, Nat.mod_eq_of_lt (hd j)]

theorem fld_eq_digit (c s : ℕ) : fld c (8 * s) 255 = c / 256 ^ s % 256 := by
  unfold fld
  change (c >>> (8 * s)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem cntW_eq (W : ℕ → ℕ) (el sz : ℕ) (ha : ∀ p < 24, pop24 (orbW W el sz p) < 25) :
    ∀ m ≤ 24, Nat.rec (motive := fun _ => ℕ) 0
      (fun p acc => acc + 1 <<< (8 * pop24 (orbW W el sz p))) m =
      ∑ s ∈ Finset.range 25,
        ((Finset.range m).filter fun p => pop24 (orbW W el sz p) = s).card * 256 ^ s := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    change Nat.rec (motive := fun _ => ℕ) 0
      (fun p acc => acc + 1 <<< (8 * pop24 (orbW W el sz p))) m +
        1 <<< (8 * pop24 (orbW W el sz m)) = _
    have hc : ∀ s, ((insert m (Finset.range m)).filter fun p => pop24 (orbW W el sz p) = s).card =
        ((Finset.range m).filter fun p => pop24 (orbW W el sz p) = s).card +
          if pop24 (orbW W el sz m) = s then 1 else 0 := by
      intro s
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    rw [ih (by omega), Finset.range_add_one (n := m)]
    simp only [hc, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_range, ha m (by omega), if_true]
    rw [Nat.one_shiftLeft, pow_mul]
    norm_num

theorem prof_sound {Γ : Type*} [Group Γ] [MulAction Γ (Fin 24)] (W : ℕ → ℕ) (u : ℕ → Γ) (f : ℕ)
    (E : Subgroup Γ) (hu : ∀ i ∈ recS REC f, ∀ p : Fin 24, ((u i • p : Fin 24) : ℕ) = img (W i) p)
    (hE : ∀ x, x ∈ E ↔ x = 1 ∨ ∃ i ∈ recS REC f, u i = x) (h31 : 31 ≤ recSz REC f)
    (hp : profW W f = true) : ProfileOK E := by
  classical
  have horb : ∀ p : Fin 24, ∀ q : ℕ, (orbW W (REC f >>> 576) (recSz REC f) p).testBit q = true ↔
      ∃ r ∈ orbitSet E p, (r : ℕ) = q := by
    intro p q
    rw [orbW_testBit]
    constructor
    · rintro (h | ⟨t, ht, e⟩)
      · exact ⟨p, self_mem_orbitSet E p, h⟩
      · have hi : recEnt REC f t ∈ recS REC f := Finset.mem_image.2 ⟨t, Finset.mem_range.2 ht, rfl⟩
        refine ⟨u (recEnt REC f t) • p, mem_orbitSet.2 ⟨_, (hE _).2 (Or.inr ⟨_, hi, rfl⟩), rfl⟩, ?_⟩
        rw [hu _ hi p]
        exact e
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨g, hg, rfl⟩ := mem_orbitSet.1 hr
      rcases (hE g).1 hg with rfl | ⟨i, hi, rfl⟩
      · left
        simp
      · right
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hi
        exact ⟨t, Finset.mem_range.1 ht, (hu _ hi p).symm⟩
  have hcard : ∀ p : Fin 24, pop24 (orbW W (REC f >>> 576) (recSz REC f) p) = (orbitSet E p).card := by
    intro p
    rw [pop24_eq, ← Finset.card_map (s := orbitSet E p) Fin.valEmbedding]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Fin.valEmbedding_apply]
    rw [horb p q]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r.isLt, r, hr, rfl⟩
  have ha : ∀ p < 24, pop24 (orbW W (REC f >>> 576) (recSz REC f) p) < 25 := by
    intro p hp
    have e := hcard ⟨p, hp⟩
    have h2 : (orbitSet E ⟨p, hp⟩).card ≤ 24 := (Finset.card_le_univ _).trans (by simp)
    change pop24 (orbW W (REC f >>> 576) (recSz REC f) (⟨p, hp⟩ : Fin 24)) < 25
    omega
  have hcnt : cntW W (REC f >>> 576) (recSz REC f) = ∑ s ∈ Finset.range 25,
      ((Finset.range 24).filter fun p => pop24 (orbW W (REC f >>> 576) (recSz REC f) p) = s).card *
        256 ^ s := cntW_eq W _ _ ha 24 le_rfl
  have hpts : ∀ s, ptsOfSize E s = ((Finset.range 24).filter
      fun p => pop24 (orbW W (REC f >>> 576) (recSz REC f) p) = s).card := by
    intro s
    unfold ptsOfSize
    rw [← Finset.card_map Fin.valEmbedding]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨r.isLt, ?_⟩
      rw [hcard r]
      exact hr
    · rintro ⟨hq, h⟩
      refine ⟨⟨q, hq⟩, ?_, rfl⟩
      rw [← hcard]
      exact h
  have hdig : ∀ s < 25, fld (cntW W (REC f >>> 576) (recSz REC f)) (8 * s) 255 = ptsOfSize E s := by
    intro s hs
    rw [fld_eq_digit, hcnt, hpts]
    exact digit_sum _ (fun s => (Finset.card_filter_le _ _).trans_lt (by simp)) 25 s hs
  unfold profW at hp
  rw [CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq] at hp
  have h31' : Nat.ble 31 (recSz REC f) = true := by
    rw [Nat.ble_eq]
    exact h31
  have hp2 := CFSG.KC.LQT.P.impB_iff.1 hp h31'
  rw [CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq] at hp2
  have hp3 : orB (andB (Nat.blt 0 (ptsOfSize E 2)) (Nat.ble (ptsOfSize E 2) 10))
      (orB (andB (Nat.blt 0 (ptsOfSize E 4)) (Nat.ble (ptsOfSize E 4) 20))
        (orB (Nat.beq (ptsOfSize E 4) 24) (Nat.beq (ptsOfSize E 8) 24))) = true := by
    rw [← hdig 2 (by norm_num), ← hdig 4 (by norm_num), ← hdig 8 (by norm_num)]
    exact hp2
  unfold ProfileOK
  rcases CFSG.KC.LQT.P.orB_iff.1 hp3 with h | h
  · obtain ⟨a1, a2⟩ := CFSG.KC.LQT.P.andB_iff.1 h
    rw [Nat.ble_eq] at a2
    exact Or.inl ⟨CFSG.KC.LQT.P.blt_iff.1 a1, a2⟩
  rcases CFSG.KC.LQT.P.orB_iff.1 h with h | h
  · obtain ⟨a1, a2⟩ := CFSG.KC.LQT.P.andB_iff.1 h
    rw [Nat.ble_eq] at a2
    exact Or.inr (Or.inl ⟨CFSG.KC.LQT.P.blt_iff.1 a1, a2⟩)
  rcases CFSG.KC.LQT.P.orB_iff.1 h with h | h
  · exact Or.inr (Or.inr (Or.inl (CFSG.KC.LQT.P.beq_iff.1 h)))
  · exact Or.inr (Or.inr (Or.inr (CFSG.KC.LQT.P.beq_iff.1 h)))

theorem m24_profile_kc :
    ∀ E : Subgroup ↥NativeSporadic.M24, IsElemAbelian 2 E → 32 ≤ Nat.card E → ProfileOK E := by
  classical
  obtain ⟨hcardR, hea⟩ := r_ea
  set R := Subgroup.closure {g | g ∈ gensR} with hR
  intro E hE h32
  have hidx : R.index = 239085 := by
    have h1 := R.card_mul_index
    rw [hcardR, card_M24] at h1
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRsyl : CFSG.QuasithinUnique.IsSylowTwoOf R ⊤ := ⟨le_top,
    IsPGroup.of_card (n := 10) (by rw [hcardR]; norm_num), by
      rw [show (R.subgroupOf ⊤).index = R.index from Subgroup.relIndex_top_right R, hidx]
      decide⟩
  have hE2 : IsPGroup 2 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨P, hEP⟩ := hE2.exists_le_sylow
  have hPsyl : CFSG.QuasithinUnique.IsSylowTwoOf (P : Subgroup Γ24) ⊤ := ⟨le_top, P.isPGroup', by
    rw [show ((P : Subgroup Γ24).subgroupOf ⊤).index = (P : Subgroup Γ24).index from
      Subgroup.relIndex_top_right _]
    exact Sylow.not_dvd_index P⟩
  obtain ⟨g, hg⟩ :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf hRsyl hPsyl
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'R : E' ≤ R := by
    rintro _ ⟨y, hy, rfl⟩
    have hyP : y ∈ (P : Subgroup Γ24) := hEP hy
    rw [← hg] at hyP
    obtain ⟨r, hr, rfl⟩ := hyP
    have h1 : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom r) = r := by
      simp [mul_assoc]
    rw [h1]
    exact hr
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcommE : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨x0, hx0, rfl⟩ _ ⟨y0, hy0, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hE.1.is_comm.comm (⟨x0, hx0⟩ : E) ⟨y0, hy0⟩))
  have hsqE : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨x0, hx0, rfl⟩
    rw [← map_mul, ← sq, hE.2 x0 hx0, map_one]
  obtain ⟨f, hf, hmem⟩ := hea E' hE'R hcommE hsqE
  have hsz : 31 ≤ recSz REC f := by
    have h1 := card_le E' hmem
    have h2 := card_recS f
    omega
  have hp := prof_sound V vv f E' (fun i hi p => by
    rw [← enc_vv (ent_lt f hf i hi)]
    exact (pcode_img (by norm_num) (vv i : Perm (Fin 24)) p).symm) hmem hsz (prof_all f hf)
  exact ProfileOK.of_map_conj (g := g⁻¹) hp

end CertificateChecks.KernelEaLat318002

end
