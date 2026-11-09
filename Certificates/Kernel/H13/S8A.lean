module

public import CFSG.Quasithin.H13.L32NS8Inputs
public import Certificates.Kernel.H13.ElemsS8
public import Certificates.Kernel.H13.DataS8C
public import CFSG.Certificates.Kernel.Mat8PSet
public import Mathlib

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S8Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000

@[expose] noncomputable def s8ClRow (T : S8T) (n x : ℕ) (k : List ℕ → Bool) (gp : List (ℕ → ℕ)) :
    List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) k
    (fun g _ ih cs => List.rec (motive := fun _ => Bool) false
      (fun c cs' _ => Nat.blt c n && (Nat.beq (s8GetT T c) (g x) && ih cs')) cs) gp

@[expose] noncomputable def s8ClChk (T : S8T) (n : ℕ) (gp : List (ℕ → ℕ)) (xs : List ℕ) :
    List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
    (fun x _ ih => s8ClRow T n x ih gp) xs

theorem s8ClRow_sound (T : S8T) (n x : ℕ) (k : List ℕ → Bool) :
    ∀ (gp : List (ℕ → ℕ)) (cs : List ℕ), s8ClRow T n x k gp cs = true →
      (∀ g ∈ gp, ∃ c < n, s8GetT T c = g x) ∧ ∃ cs', k cs' = true
  | [], cs, h => ⟨fun _ hg => absurd hg List.not_mem_nil, cs, h⟩
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | g :: gp, c :: cs, h => by
    have h' : (Nat.blt c n && (Nat.beq (s8GetT T c) (g x) && s8ClRow T n x k gp cs)) =
        true := h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨hc, he, hr⟩ := h'
    obtain ⟨hgp, hk⟩ := s8ClRow_sound T n x k gp cs hr
    refine ⟨fun g' hg' => ?_, hk⟩
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact ⟨c, hc, he⟩
    · exact hgp g' hg'

theorem s8ClChk_sound (T : S8T) (n : ℕ) (gp : List (ℕ → ℕ)) :
    ∀ (xs cs : List ℕ), s8ClChk T n gp xs cs = true →
      ∀ x ∈ xs, ∀ g ∈ gp, ∃ c < n, s8GetT T c = g x
  | [], _, _ => fun _ hx => absurd hx List.not_mem_nil
  | x :: xs, cs, h => by
    have h' : s8ClRow T n x (s8ClChk T n gp xs) gp cs = true := h
    obtain ⟨hx, cs', hr⟩ := s8ClRow_sound T n x _ gp cs h'
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact s8ClChk_sound T n gp xs cs' hr y hy

theorem closedP_of_s8ClChk (gp L cs : List ℕ) (fs : List (ℕ → ℕ))
    (hfs : ∀ g ∈ gp, ∃ f ∈ fs, ∀ x ∈ L, mulP g x = f x)
    (h : s8ClChk (s8OfT L.length L) L.length fs L cs = true) : closedP gp L = true := by
  rw [closedP, List.all_eq_true]
  intro x hx
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨f, hf, hgf⟩ := hfs g hg
  obtain ⟨c, hc, he⟩ := s8ClChk_sound _ _ fs L cs h x hx f hf
  rw [hgf x hx, memP_ofListP, ← he, s8GetT_ofT _ _ le_rfl, List.getD_eq_getElem _ _ hc,
    List.contains_iff_mem]
  exact List.getElem_mem hc

@[expose] noncomputable def s8SrtChk (T : S8T) (n : ℕ) : List ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun c _ ih lo => Nat.blt c n && (Nat.blt lo (s8GetT T c) && ih (s8GetT T c)))

theorem s8SrtChk_sound (T : S8T) (n : ℕ) :
    ∀ (σ : List ℕ) (lo : ℕ), s8SrtChk T n σ lo = true →
      (∀ c ∈ σ, c < n) ∧ (σ.map (s8GetT T)).Pairwise (· < ·) ∧ ∀ v ∈ σ.map (s8GetT T), lo < v
  | [], _, _ =>
    ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | c :: σ, lo, h => by
    have h' : (Nat.blt c n && (Nat.blt lo (s8GetT T c) && s8SrtChk T n σ (s8GetT T c))) =
        true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨hc, hlo, hr⟩ := h'
    obtain ⟨h1, h2, h3⟩ := s8SrtChk_sound T n σ _ hr
    refine ⟨fun c' hc' => ?_, ?_, fun v hv => ?_⟩
    · rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hc
      · exact h1 c' hc'
    · rw [List.map_cons, List.pairwise_cons]
      exact ⟨h3, h2⟩
    · rw [List.map_cons] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hlo
      · exact lt_trans hlo (h3 v hv)

theorem nodup_of_s8SrtChk (L σ : List ℕ) (hl : σ.length = L.length)
    (h : s8SrtChk (s8OfT L.length L) L.length σ 0 = true) : L.Nodup := by
  obtain ⟨h1, h2, -⟩ := s8SrtChk_sound _ _ σ 0 h
  have hVn : (σ.map (s8GetT (s8OfT L.length L))).Nodup := h2.imp ne_of_lt
  have hsub : (σ.map (s8GetT (s8OfT L.length L))).toFinset ⊆ L.toFinset := by
    intro v hv
    rw [List.mem_toFinset] at hv ⊢
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    rw [s8GetT_ofT _ _ le_rfl, List.getD_eq_getElem _ _ (h1 c hc)]
    exact List.getElem_mem _
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hVn, List.length_map, hl, List.card_toFinset] at hc
  rw [← (List.dedup_sublist L).eq_of_length_le hc]
  exact List.nodup_dedup L

set_option maxRecDepth 200000 in
theorem s8SrtChk_true : s8SrtChk (s8OfT D.s8L.length D.s8L) D.s8L.length D.s8S 0 = true := by
  decide +kernel

theorem s8S_length : D.s8S.length = D.s8L.length := by
  decide +kernel

@[expose] noncomputable def s8Gb0 (x : ℕ) : ℕ :=
  Nat.xor x (Nat.xor (Nat.land (Nat.shiftRight x 1) (nat_lit 72340172838076673))
    (Nat.land (Nat.shiftLeft x 1) (nat_lit 2314885530818453536)))

@[expose] noncomputable def s8Gb1 (x : ℕ) : ℕ :=
  Nat.xor x (Nat.xor (Nat.land (Nat.shiftRight x 1) (nat_lit 144680345676153346))
    (Nat.land (Nat.shiftLeft x 1) (nat_lit 4629771061636907072)))

@[expose] noncomputable def s8Gb2 (x : ℕ) : ℕ :=
  Nat.xor x (Nat.xor (Nat.land (Nat.shiftRight x 1) (nat_lit 289360691352306692))
    (Nat.land (Nat.shiftLeft x 1) (nat_lit 9259542123273814144)))

@[expose] noncomputable def s8Gb3 (x : ℕ) : ℕ :=
  Nat.xor x (Nat.xor (Nat.land (Nat.shiftLeft x 3) (nat_lit 578721382704613384))
    (Nat.land (Nat.shiftRight x 3) (nat_lit 1157442765409226768)))

@[expose] noncomputable def s8Gb4 (x : ℕ) : ℕ :=
  Nat.xor (Nat.land (Nat.shiftLeft x 4) (nat_lit 17361641481138401520))
    (Nat.land (Nat.shiftRight x 4) (nat_lit 1085102592571150095))

theorem s8Gb_bit (G x : ℕ) (f : ℕ → ℕ) (hf : f x < 2 ^ 64)
    (h : ∀ j < 8, ∀ b < 8, (mulPs G x).testBit (8 * j + b) = (f x).testBit (8 * j + b)) :
    mulP G x = f x := by
  rw [mulP_eq]
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 64
  · rw [← Nat.div_add_mod n 8]
    exact h _ (by omega) _ (Nat.mod_lt _ (by norm_num))
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (mulP_eq G x ▸ mulP_lt G x)
      (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hf (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem s8Gb_mask (M c j b : ℕ) (hM : M = 72340172838076673 * c) (hc : c < 2 ^ 8) (hj : j < 8)
    (hb : b < 8) : M.testBit (8 * j + b) = c.testBit b := by
  have h := lanes_mul_testBit 8 (lanes 8) c hc j b hb
  rw [hM]
  rw [Nat.and_self, lanes_eight] at h
  have h8 : (72340172838076673 : ℕ).testBit (8 * j) = true := by
    interval_cases j <;> decide
  rw [h, h8]
  simp [hj]

theorem s8Gb_and_lt (x m : ℕ) (hm : m < 2 ^ 64) : x &&& m < 2 ^ 64 :=
  lt_of_le_of_lt Nat.and_le_right hm

theorem mulP_s8Gb0 (x : ℕ) (hx : x < 2 ^ 64) : mulP 9241421826029257473 x = s8Gb0 x := by
  have e : s8Gb0 x = x ^^^ (((x >>> 1) &&& 72340172838076673) ^^^
      ((x <<< 1) &&& 2314885530818453536)) := rfl
  refine s8Gb_bit _ x s8Gb0 (e ▸ Nat.xor_lt_two_pow hx (Nat.xor_lt_two_pow
    (s8Gb_and_lt _ _ (by norm_num)) (s8Gb_and_lt _ _ (by norm_num)))) fun j hj b hb => ?_
  simp only [e, mulPs, Nat.testBit_xor, term_testBit _ _ _ j b hj hb, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    s8Gb_mask 72340172838076673 1 j b rfl (by norm_num) hj hb,
    s8Gb_mask 2314885530818453536 32 j b rfl (by norm_num) hj hb]
  interval_cases b <;> simp +arith [Nat.testBit, Bool.xor_comm]

theorem mulP_s8Gb1 (x : ℕ) (hx : x < 2 ^ 64) : mulP 9241492057334612481 x = s8Gb1 x := by
  have e : s8Gb1 x = x ^^^ (((x >>> 1) &&& 144680345676153346) ^^^
      ((x <<< 1) &&& 4629771061636907072)) := rfl
  refine s8Gb_bit _ x s8Gb1 (e ▸ Nat.xor_lt_two_pow hx (Nat.xor_lt_two_pow
    (s8Gb_and_lt _ _ (by norm_num)) (s8Gb_and_lt _ _ (by norm_num)))) fun j hj b hb => ?_
  simp only [e, mulPs, Nat.testBit_xor, term_testBit _ _ _ j b hj hb, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    s8Gb_mask 144680345676153346 2 j b rfl (by norm_num) hj hb,
    s8Gb_mask 4629771061636907072 64 j b rfl (by norm_num) hj hb]
  interval_cases b <;> simp +arith [Nat.testBit, Bool.xor_comm]

theorem mulP_s8Gb2 (x : ℕ) (hx : x < 2 ^ 64) : mulP 9277450485676376577 x = s8Gb2 x := by
  have e : s8Gb2 x = x ^^^ (((x >>> 1) &&& 289360691352306692) ^^^
      ((x <<< 1) &&& 9259542123273814144)) := rfl
  refine s8Gb_bit _ x s8Gb2 (e ▸ Nat.xor_lt_two_pow hx (Nat.xor_lt_two_pow
    (s8Gb_and_lt _ _ (by norm_num)) (s8Gb_and_lt _ _ (by norm_num)))) fun j hj b hb => ?_
  simp only [e, mulPs, Nat.testBit_xor, term_testBit _ _ _ j b hj hb, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    s8Gb_mask 289360691352306692 4 j b rfl (by norm_num) hj hb,
    s8Gb_mask 9259542123273814144 128 j b rfl (by norm_num) hj hb]
  interval_cases b <;> simp +arith [Nat.testBit, Bool.xor_comm]

theorem mulP_s8Gb3 (x : ℕ) (hx : x < 2 ^ 64) : mulP 10394343193197150729 x = s8Gb3 x := by
  have e : s8Gb3 x = x ^^^ (((x <<< 3) &&& 578721382704613384) ^^^
      ((x >>> 3) &&& 1157442765409226768)) := rfl
  refine s8Gb_bit _ x s8Gb3 (e ▸ Nat.xor_lt_two_pow hx (Nat.xor_lt_two_pow
    (s8Gb_and_lt _ _ (by norm_num)) (s8Gb_and_lt _ _ (by norm_num)))) fun j hj b hb => ?_
  simp only [e, mulPs, Nat.testBit_xor, term_testBit _ _ _ j b hj hb, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    s8Gb_mask 578721382704613384 8 j b rfl (by norm_num) hj hb,
    s8Gb_mask 1157442765409226768 16 j b rfl (by norm_num) hj hb]
  interval_cases b <;> simp +arith [Nat.testBit, Bool.xor_comm]

theorem mulP_s8Gb4 (x : ℕ) : mulP 577588857680175120 x = s8Gb4 x := by
  have e : s8Gb4 x = ((x <<< 4) &&& 17361641481138401520) ^^^
      ((x >>> 4) &&& 1085102592571150095) := rfl
  refine s8Gb_bit _ x s8Gb4 (e ▸ Nat.xor_lt_two_pow (s8Gb_and_lt _ _ (by norm_num))
    (s8Gb_and_lt _ _ (by norm_num))) fun j hj b hb => ?_
  simp only [e, mulPs, Nat.testBit_xor, term_testBit _ _ _ j b hj hb, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    s8Gb_mask 17361641481138401520 240 j b rfl (by norm_num) hj hb,
    s8Gb_mask 1085102592571150095 15 j b rfl (by norm_num) hj hb]
  interval_cases b <;> simp +arith [Nat.testBit, Bool.xor_comm]

theorem s8Gb_mulP : ∀ g ∈ s8G.map code64R, ∃ f ∈ [s8Gb0, s8Gb1, s8Gb2, s8Gb3, s8Gb4],
    ∀ x ∈ D.s8L, mulP g x = f x := by
  have e : s8G.map code64R = [9241421826029257473, 9241492057334612481, 9277450485676376577,
      10394343193197150729, 577588857680175120] := by decide
  rw [e]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact ⟨s8Gb0, by simp, fun x hx => mulP_s8Gb0 x (s8L_lt x hx)⟩
  · exact ⟨s8Gb1, by simp, fun x hx => mulP_s8Gb1 x (s8L_lt x hx)⟩
  · exact ⟨s8Gb2, by simp, fun x hx => mulP_s8Gb2 x (s8L_lt x hx)⟩
  · exact ⟨s8Gb3, by simp, fun x hx => mulP_s8Gb3 x (s8L_lt x hx)⟩
  · exact ⟨s8Gb4, by simp, fun x _ => mulP_s8Gb4 x⟩

set_option maxRecDepth 200000 in
theorem s8ClChk_true : s8ClChk (s8OfT D.s8L.length D.s8L) D.s8L.length
    [s8Gb0, s8Gb1, s8Gb2, s8Gb3, s8Gb4] D.s8L D.s8C = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem s8_basicB_true : s8BasicB = true := by
  rw [s8BasicB, s8E_eq, unpack_code64R_map s8G (by decide), subB, all_validB_map,
    all_validB_map, closedB_map _ _ s8L_lt, nodupB_map _ s8L_lt, contains_map _ s8L_lt,
    List.length_map, closedP_of_s8ClChk _ _ _ _ s8Gb_mulP s8ClChk_true,
    (nodupP_iff _).2 (nodup_of_s8SrtChk _ _ s8S_length s8SrtChk_true)]
  decide +kernel

macro "s8_tac" : tactic => `(tactic| (
  simp only [orbB, zB, nB, CFSG.Quasithin.H13.S8Cert.wB, fB, stE, invSt, eSpan8, nodupN,
    s8E_eq, subB, closedB, nodupB_toP, elemsOf_toF, decide_isChain_toP, List.any_map,
    Function.comp_def, hs_contains_toLR', hs_contains_toLR, contains_toLR, hsN_contains_toP',
    hsN_contains_toP, mul8_toF, mv8_toR]
  decide +kernel))

@[expose] noncomputable def s8SubChk : List ℕ → List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool)
    (fun ws => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ws)
    (fun x _ ih ws => List.rec (motive := fun _ => Bool) true
      (fun a ws' _ => Bool.rec (motive := fun _ => Bool) (ih (a :: ws')) (ih ws') (Nat.beq a x)) ws)

theorem s8SubChk_sound : ∀ (l ws : List ℕ), s8SubChk l ws = true → ws.Sublist l
  | [], [], _ => List.Sublist.slnil
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _ => List.nil_sublist _
  | x :: l, a :: ws, h => by
    change Bool.rec (motive := fun _ => Bool) (s8SubChk l (a :: ws)) (s8SubChk l ws)
      (Nat.beq a x) = true at h
    cases hb : Nat.beq a x
    · rw [hb] at h
      exact (s8SubChk_sound l _ h).cons x
    · rw [hb] at h
      rw [Nat.eq_of_beq_eq_true hb]
      exact (s8SubChk_sound l ws h).cons_cons x

@[expose] def s8OrbW : List ℕ :=
  [146649580103045184, 2310487758747011076, 2346516418259912964, 2310557989985126412,
    144405476863410240, 144970637919682624, 216463105263190080, 144405525186003008,
    723118063340286016, 1081154199358578784, 216464174722613312, 144976136555757760,
    721433577435214064, 868359161255084064, 576757640308203616, 720866263526596672,
    864981426906390560, 144405515522326592, 2328501813592197125, 795175657380302912,
    288520656886202400, 434887657130094688, 146657290639953984, 2310487689960687620,
    290772474416631840, 723118038644224064, 16145616045267290636, 147783163702198352,
    4625285740430494472, 16181697618962418438, 5791787931610712079, 16172690900643351814,
    6976164402236950791, 5814217968766684426, 5778277613848823567, 17298520095328896522,
    289083659184549936, 288520713259753504, 795167965105393728, 361143453328896240,
    146376901220372544, 2328501951115036677, 146657280976277568, 11533754792341998084,
    1009096631625228384, 5832232367276164362, 12686781918684056068, 720866273190256704,
    3499437991586631428, 434887644775747680, 2346516555765975300, 6922173502262937606,
    434892083906515184, 4620711359691227400, 4625285465686805256, 146376910884048960,
    2346517036735465732, 2342030410819109124, 8129156000709936395, 8106726307083781382,
    9228051833388335620, 11533859795601788420, 940705892231311552, 794895247561732160,
    9273087829662040836, 362274835761516624, 576753277695172672, 148350537749778624,
    11578896272928869892, 1009663982577955008, 2337545090723024133, 146657324999675968,
    432635849263317088, 2360027285861764353, 722837687889825856, 11542867613281750788,
    1081154191307620448, 793487910531772480, 1013037250972270688, 433757376358707328,
    505820475741458640, 432631504369115264, 16195032908401606925, 289920387274248320,
    15001701877573093132, 15055745416497596684, 6931251688721221391, 937609688157024448,
    290201866545934464, 12718254339501196039, 435454996816883936, 218434509219049536,
    508352618799607904, 363385304117203104, 434607269319020640, 6958202299281901830,
    2342030548325171460, 8106725757328098566, 289089143866142896, 436013539856015472,
    648811975548084288, 1009383604438962368, 506670360113991776, 508630797394128976,
    6962653122368373007]

theorem s8OrbW_sub : s8SubChk D.s8L s8OrbW = true := by
  decide +kernel

theorem s8OrbW_chk : (List.range 256).all (fun v => v == 0 || inII v || q4N v ||
    (s8OrbW.map fun p => mv8R (unpackM p) vR).contains v) = true := by
  decide +kernel

theorem s8_orbB_true : orbB = true := by
  have hs := s8SubChk_sound _ _ s8OrbW_sub
  simp only [orbB, List.all_eq_true]
  intro v hv
  have h := List.all_eq_true.mp s8OrbW_chk v hv
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rw [Std.HashSet.contains_ofList, s8E_eq, List.map_map, List.contains_iff_mem]
    rw [List.contains_iff_mem] at h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨p, hs.subset hp, by simp only [Function.comp_def, mv8R_eq]⟩

set_option maxHeartbeats 0 in
theorem s8_wB_true : CFSG.Quasithin.H13.S8Cert.wB = true := by s8_tac

set_option maxHeartbeats 0 in
theorem s8_fB_true : fB = true := by s8_tac

@[expose] def s8StL : List ℕ :=
  [434607269319020640, 291050633417461920, 435174617587388640, 435165821493317872,
    291061628534788256, 436296121595203680, 436302718396534880, 435170219272442096,
    292187530320679072, 291055031196586160, 435168020516573408, 435172418295697632,
    435176816610644208, 435161423178371296, 291059429511532720, 434611667633967216,
    290496479558111264, 290492081243164704, 291046235102515360, 291057230219841696,
    290487683464040480, 434602871539896432, 434598473224949856, 435737569419858144,
    435733171641782512, 434613866657222752, 435728773594222832, 434605070563151968,
    292176535471788192, 436293922570899552, 291052832440717488, 292180933519347888,
    435730972617478368, 435735370665038048, 435739768443113712, 435724375279276256,
    290489882487296048, 291048434125770928, 290483285149093920, 290494280266420272,
    434600672248205424, 866952833550782496, 1011059225532567648, 1011068021626638432,
    292185331297423536, 436300519373279344, 291622381344002080, 434609468342276208,
    435163622201626864, 290498678581366832, 436298320618459248, 291617983565926432,
    436287325232697440, 292183132542603424, 292172137156841632, 436291723547644016,
    291613585518366752, 292178734495043760, 1009937724747026592, 579848359712395296,
    580402513304359008, 291620182589182000, 436289524255953008, 865826934986117152,
    1010496276652888160, 4670408804398662155, 867506987410133216, 1011622175485989024,
    1011626573801984160, 4652394405721408011, 578159508778389600, 866381088577032416,
    865822536671170592, 13875836811354046989, 15028758315960893963, 4652341629196698123,
    5805315910328254991, 15010691140960518663, 5823330309005509125, 723967945567375584,
    578157309487747168, 5805263133803545101, 724517701380214944, 867520181818101984,
    1009942123061973168, 866944037456711712, 290485484172349488, 723963547788251376,
    1011635369893957808, 5823277532447244805, 866957231864680480, 5800900271664660997,
    577600956872527904, 866948435772706848, 580417906468196448, 579843961666932768,
    867513584749383904, 13875713666051867149, 4652464774499140107, 5800759534176174597,
    5805403871292031503, 1010505073015394400, 5800829902886928903, 580411309665816672,
    13875766442576445967, 15024272308519567877, 5823400677716132359, 5818844301564183053,
    721707348586926240, 1010502873723703392, 865831333031579680, 721711746900824240,
    1009933326699466912, 722265900492787936, 13875854403540091407, 13857840005097718287,
    291609187203420192, 5823347901191553543, 15010743917518520839, 435726574302531824,
    291615784541622320, 15010761509704565253, 13857752044167627279, 292174336180097200,
    13857769636353671693, 291624580367257648, 723954751426793696, 579852757491519520,
    13857699267575939597, 4670426396584706569, 13857822412911673869, 5823259940261200391,
    4670356027840397835, 15006240317891150347, 721702950539366560, 1010511670084112480,
    5823418269902176773, 5818826709378138639, 5818914670274806287, 15024201939741966855,
    13875784034762490381, 5800812310700884485, 15024254716333523463, 722279094901805280,
    5800882679478616583, 5800741941990130183, 5800689165398442503, 13875696073865822735,
    580409110643609696, 13875643297274003983, 1011065822871818336, 15006169949147103755,
    15024131571031343621, 1011074618963791968, 15006257910077194761, 5823207163669512711,
    5818773932819874317, 867522380841357552, 1011072419940536432, 867517982527459552,
    1011070220649894000, 4647978767057814019, 721716144948383920, 15006187541333148169,
    1011063623848562800, 867511385726128368, 5805192765025813007, 9282094822825656837,
    722272497563603168, 15010603179996742151, 724533094544052384, 723959149742788848,
    1011628772825239728, 15010673548774474245, 15028635170658714123, 5805386279105987085,
    1011633170603315360, 1011637568917213344, 4652271260418966027, 4647838029569327619,
    5805245541617500687, 4652324037010653705, 4652482366685184521, 577592160511070240,
    866389884939538672, 866394282985001184, 4652411997907452425, 5805333502514299405,
    4647908398280081923, 724522099696210080, 1011630971580059824, 15028775908146938377,
    724526497741672624, 15010620772182786565, 15028687947183292939, 13871350803912720899,
    867515783504204016, 4670479173109285387, 4665922796957336067, 13857681675389895183,
    865818138623610912, 291611386226675760, 722281293925060848, 578150712416931936,
    578166105849204832, 577596558824968224, 722274696854245616, 866387685647847648,
    1009946521107435696, 579839563350937632, 866396482008256752, 1010509471060856944,
    866392083962794208, 1010507272038649968, 4665993165667959299, 580415707444940912,
    724530895520796848, 13871280435135119875, 15028705539369337353, 4647890806094037505,
    13871333211726676481, 1010500674700447856, 866385486624592112, 578163906825949296,
    4647961174871769601, 4652253668232921609, 4647820437383283201, 5805175172839768589,
    4647767660791595523, 724528696764928160, 1011624374509244592, 15028617578472669705,
    724524298719465648, 15010532811252433413, 10435016327432503819, 9282165191536411143,
    15028564801880850955, 580406911620354160, 866950634795962416, 13853248444540256769,
    10430530319991177741, 9282042046267654661, 13871210066424496643, 10434963550874501643,
    866955032574038064, 867509186433388784, 866959430887936048, 580413508689072240,
    5818703564042142223, 723965746811506912, 1011061424555823216, 723961348766044384,
    10399075491276784143, 9246066025739584005, 15024061202253480455, 13875625705087959565,
    5800671573212398085, 15024113978845299207, 721718343971639456, 722270298540347632,
    1009939923770282160, 15024184347555922437, 9246083617925628423, 723970144590631152,
    15006117172555416075, 5818897078088761869, 10430600688701932047, 1009944322085228704,
    1009948720130691232, 722276895877501152, 13853336405470347779, 9277608815384330755,
    4670285659062665739, 4665852428213027331, 15010550403438477831, 13853266036726301187,
    5823189571483468293, 5818756340633829903, 13853318813284303361, 13857611306645586445,
    4670338435654353417, 4670496765295329801, 4665905204771291649, 13857628898831630863,
    9281971677489791495, 577587762463510560, 9245942880403718663, 4665975573481914881,
    4670268066876621321, 4665834836026982913, 5818685971856097805, 4665782059435295235,
    9241580018298257923, 721713945924079776, 722268099516043504, 1009935525722722480,
    10394431154127503883, 15006099580369371657, 9282112415011701255, 721709547610181808,
    10430389582469267983, 15024043610067436037, 9246136394483892743, 9241650387042566659,
    10394483930719060491, 723956950450049264, 15006046803811107339, 579850558735650864,
    580404712327614576, 866946236479967280, 9277538446640284163, 10430459951247131149,
    10394501522905104905, 579846160690188336, 10434893182096638475, 9245995656961982983,
    10435086696143258123, 9246153986669937157, 10398987530346430991, 724519900403470512,
    13871139697646633475, 15028547209694806537, 4647750068605551105, 13871192474238452225,
    577603155895783472, 578155110464491632, 865824735694426160, 9277679184095085059,
    13871262842949075457, 10399005122532475405, 9246013249148027397, 10398864385010565647,
    579854956514775088, 13853195667948569091, 865829134009372720, 1010498475676143728,
    866383287600287984, 865833532054835248, 578161707801645168, 577598757848223792,
    578152911440187504, 865820337646866480, 10398934753754874381, 10435033919618548233,
    577594359534325808, 13871122105460589057, 10399057899090739725, 10398917161568829967,
    10394571891649413641, 9241562426112213505, 579841762374193200, 10394554299463369227,
    9245925288217674245, 9282024454081610247, 9282182783722455557, 10430512727805133327,
    721705149562622128, 13853125299204260355, 15006029211625062921, 4665764467249250817,
    13853178075762524673, 10394360785383195147, 9277468077862420995, 9241509649520656899,
    9241439280776348163, 13853107707018215937, 10430583096515887629, 9281954085303747077,
    10430442359061086735, 9241632794856522241, 10398846792824521229, 10434945958688457225,
    10435104288329302537, 9277591223198286337, 577589961486766128, 9277661591909040641,
    10434875589910594057, 9277520854454239745, 10430371990283223565, 10394413561941459465,
    10394343193197150729, 9277450485676376577, 9241492057334612481, 9241421688590303745]

theorem mv8R_unpackM_vR (p : ℕ) : mv8R (unpackM p) vR =
    Nat.xor (Nat.land (Nat.shiftRight p 8) 255) (Nat.land (Nat.shiftRight p 32) 255) := by
  simp only [unpackM, mv8R, vR]
  norm_num

theorem s8StL_eqF : D.s8L.filter (fun p =>
    Nat.xor (Nat.land (Nat.shiftRight p 8) 255) (Nat.land (Nat.shiftRight p 32) 255) == 18) =
      s8StL := by
  decide +kernel

theorem s8StL_eq : D.s8L.filter (fun p => mv8R (unpackM p) vR == vR) = s8StL := by
  simp only [mv8R_unpackM_vR]
  exact s8StL_eqF

theorem stE_eqL : stE = s8StL.map unpackM := by
  rw [stE, s8E_eq, List.filter_map, ← s8StL_eq]
  simp only [Function.comp_def, mv8R_eq]

theorem getD_map_unpackM (o : Option ℕ) :
    (o.map unpackM).getD (unpackM oneP) = unpackM (o.getD oneP) := by
  cases o <;> rfl

theorem beq_mulP_one (a b : ℕ) : (unpackM (mulP a b) == unpackM oneP) = (mulP a b == oneP) :=
  unpackM_beq (mulP_lt a b) oneP_lt

theorem invSt_unpackM (q : ℕ) :
    invSt (unpackM q) = unpackM ((s8StL.find? fun m => mulP m q == oneP).getD oneP) := by
  rw [invSt, stE_eqL, List.find?_map, ← oneP_eq, ← getD_map_unpackM]
  simp only [Function.comp_def, mul8_unpackM, beq_mulP_one]

theorem n8G_valid : n8G.all validB = true := by decide

theorem z8G_valid : z8G.all validB = true := by decide

theorem elemsF_valid {gens : List (List ℕ)} (h : gens.all validB = true) (cap : ℕ) :
    elemsF gens cap = (elemsP (gens.map code64R) cap).map unpackM := by
  simp only [elemsF, h, ↓reduceIte]

@[expose] noncomputable def s8InvChk (T : NT ℕ) : List ℕ → List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
    (fun n _ ih I => List.rec (motive := fun _ => Bool) false
      (fun m I' _ => memP T m && (Nat.beq (mulP m n) oneP && ih I')) I)

theorem s8InvChk_sound (T : NT ℕ) : ∀ (L I : List ℕ), s8InvChk T L I = true →
    ∀ n ∈ L, ∃ m, memP T m = true ∧ mulP m n = oneP
  | [], _, _ => fun _ hn => absurd hn List.not_mem_nil
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | n :: L, m :: I, h => by
    have h' : (memP T m && (Nat.beq (mulP m n) oneP && s8InvChk T L I)) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    obtain ⟨hm, he, hr⟩ := h'
    intro n' hn'
    rcases List.mem_cons.mp hn' with rfl | hn'
    · exact ⟨m, hm, he⟩
    · exact s8InvChk_sound T L I hr n' hn'

@[expose] def s8StI : List ℕ :=
  [434607269319020640, 291050633417461920, 435174617587388640, 291059429511532720,
    435168020516573408, 435737569419858144, 436302718396534880, 434611667633967216,
    436293922570899552, 434602871539896432, 291061628534788256, 434613866657222752,
    435176816610644208, 290496479558111264, 435165821493317872, 435170219272442096,
    435161423178371296, 434598473224949856, 290487683464040480, 434605070563151968,
    291046235102515360, 291055031196586160, 290492081243164704, 436296121595203680,
    435733171641782512, 435172418295697632, 292180933519347888, 291057230219841696,
    292176535471788192, 292187530320679072, 291052832440717488, 435728773594222832,
    292183132542603424, 435735370665038048, 436298320618459248, 291617983565926432,
    291048434125770928, 290489882487296048, 290483285149093920, 434600672248205424,
    290494280266420272, 1011059225532567648, 866952833550782496, 1011068021626638432,
    436291723547644016, 436300519373279344, 436287325232697440, 434609468342276208,
    290498678581366832, 435163622201626864, 435739768443113712, 435724375279276256,
    291622381344002080, 435730972617478368, 291613585518366752, 292185331297423536,
    292172137156841632, 292178734495043760, 580411309665816672, 1009933326699466912,
    865822536671170592, 435726574302531824, 291624580367257648, 723954751426793696,
    579852757491519520, 15024272308519567877, 866948435772706848, 866957231864680480,
    867520181818101984, 5800759534176174597, 721707348586926240, 579843961666932768,
    580402513304359008, 5823330309005509125, 5818844301564183053, 5800829902886928903,
    5805263133803545101, 13857840005097718287, 13875836811354046989, 1010505073015394400,
    578157309487747168, 5805315910328254991, 865831333031579680, 1011626573801984160,
    723963547788251376, 866944037456711712, 290485484172349488, 1009942123061973168,
    1011635369893957808, 13875766442576445967, 1011622175485989024, 4652464774499140107,
    722265900492787936, 867506987410133216, 1010502873723703392, 866381088577032416,
    867513584749383904, 5823400677716132359, 5800900271664660997, 4652394405721408011,
    5805403871292031503, 723967945567375584, 4652341629196698123, 1009937724747026592,
    5823277532447244805, 4670408804398662155, 13875713666051867149, 15028758315960893963,
    578159508778389600, 580417906468196448, 724517701380214944, 721711746900824240,
    579848359712395296, 577600956872527904, 5823347901191553543, 15010691140960518663,
    291609187203420192, 13875854403540091407, 13857769636353671693, 291620182589182000,
    292174336180097200, 13857752044167627279, 15010761509704565253, 291615784541622320,
    15010743917518520839, 436289524255953008, 865826934986117152, 1010496276652888160,
    15010603179996742151, 15024254716333523463, 15010673548774474245, 13875784034762490381,
    15024201939741966855, 15006187541333148169, 577596558824968224, 724533094544052384,
    13875696073865822735, 15028775908146938377, 15028635170658714123, 4670356027840397835,
    5823259940261200391, 4652324037010653705, 4670426396584706569, 722279094901805280,
    4652482366685184521, 4652411997907452425, 4652271260418966027, 5823418269902176773,
    866387685647847648, 5823207163669512711, 867517982527459552, 15006257910077194761,
    4670479173109285387, 1011633170603315360, 15006169949147103755, 13875643297274003983,
    15028687947183292939, 1011628772825239728, 1011630971580059824, 1011065822871818336,
    1011070220649894000, 4647978767057814019, 722274696854245616, 15006240317891150347,
    867515783504204016, 867511385726128368, 5805192765025813007, 9282094822825656837,
    578166105849204832, 13857699267575939597, 1010511670084112480, 866389884939538672,
    867522380841357552, 13857822412911673869, 5818914670274806287, 5805386279105987085,
    1011074618963791968, 1011637568917213344, 5800689165398442503, 4647908398280081923,
    5805333502514299405, 5800812310700884485, 5800882679478616583, 578150712416931936,
    723959149742788848, 724522099696210080, 5800741941990130183, 5805245541617500687,
    4647838029569327619, 866394282985001184, 1011072419940536432, 5818826709378138639,
    1009946521107435696, 13857681675389895183, 5818773932819874317, 4665922796957336067,
    1011063623848562800, 15024131571031343621, 13871350803912720899, 15010620772182786565,
    579839563350937632, 291611386226675760, 722281293925060848, 577592160511070240,
    722272497563603168, 721702950539366560, 721716144948383920, 580409110643609696,
    724526497741672624, 865818138623610912, 724524298719465648, 724530895520796848,
    723961348766044384, 723970144590631152, 13871210066424496643, 1010500674700447856,
    1010509471060856944, 4665852428213027331, 5818756340633829903, 4647820437383283201,
    4665905204771291649, 580415707444940912, 580406911620354160, 722270298540347632,
    4647961174871769601, 5800671573212398085, 4647890806094037505, 5805175172839768589,
    4647767660791595523, 1009948720130691232, 866959430887936048, 5818897078088761869,
    866396482008256752, 13857611306645586445, 10430530319991177741, 9282042046267654661,
    5818703564042142223, 866385486624592112, 867509186433388784, 13853318813284303361,
    10435016327432503819, 9282165191536411143, 4665993165667959299, 10430600688701932047,
    1011061424555823216, 866950634795962416, 1011624374509244592, 1009939923770282160,
    15028564801880850955, 1009944322085228704, 866955032574038064, 866392083962794208,
    10399075491276784143, 9246066025739584005, 4670285659062665739, 5823189571483468293,
    4652253668232921609, 4670496765295329801, 722276895877501152, 578163906825949296,
    580413508689072240, 4670338435654353417, 9246083617925628423, 1010507272038649968,
    15006117172555416075, 15028617578472669705, 10434963550874501643, 723965746811506912,
    724528696764928160, 721718343971639456, 13853266036726301187, 9277608815384330755,
    15024061202253480455, 13871280435135119875, 13857628898831630863, 13853336405470347779,
    13875625705087959565, 15028705539369337353, 13853248444540256769, 15010532811252433413,
    15024184347555922437, 15024113978845299207, 13871333211726676481, 15010550403438477831,
    9281971677489791495, 577587762463510560, 9245942880403718663, 13871192474238452225,
    15024043610067436037, 13871262842949075457, 15028547209694806537, 13871139697646633475,
    9241580018298257923, 721713945924079776, 577603155895783472, 579850558735650864,
    10394431154127503883, 15006099580369371657, 9282112415011701255, 578161707801645168,
    10434893182096638475, 4670268066876621321, 9246153986669937157, 9241650387042566659,
    10394501522905104905, 865829134009372720, 15006046803811107339, 1009935525722722480,
    865824735694426160, 866946236479967280, 9277679184095085059, 10435086696143258123,
    10394483930719060491, 866383287600287984, 10430389582469267983, 9246013249148027397,
    10430459951247131149, 9246136394483892743, 10399005122532475405, 865833532054835248,
    4665782059435295235, 5818685971856097805, 4647750068605551105, 4665975573481914881,
    722268099516043504, 578155110464491632, 580404712327614576, 9277538446640284163,
    4665834836026982913, 10398987530346430991, 9245995656961982983, 10398864385010565647,
    1010498475676143728, 13853195667948569091, 723956950450049264, 579854956514775088,
    579846160690188336, 724519900403470512, 721709547610181808, 721705149562622128,
    577594359534325808, 579841762374193200, 10398917161568829967, 10430512727805133327,
    578152911440187504, 4665764467249250817, 10399057899090739725, 10398934753754874381,
    10394554299463369227, 9241562426112213505, 865820337646866480, 10394571891649413641,
    9245925288217674245, 9282182783722455557, 9282024454081610247, 10435033919618548233,
    577598757848223792, 13853125299204260355, 15006029211625062921, 13871122105460589057,
    13853178075762524673, 10394360785383195147, 9277468077862420995, 9241509649520656899,
    9241439280776348163, 13853107707018215937, 10434945958688457225, 9281954085303747077,
    10435104288329302537, 9241632794856522241, 10398846792824521229, 10430583096515887629,
    10430442359061086735, 9277591223198286337, 577589961486766128, 9277520854454239745,
    10430371990283223565, 9277661591909040641, 10434875589910594057, 10394413561941459465,
    10394343193197150729, 9277450485676376577, 9241492057334612481, 9241421688590303745]

theorem s8InvChk_true : s8InvChk (ofListP s8StL) s8StL s8StI = true := by
  decide +kernel

theorem stE_invSt : stE.all (fun n => mul8 (invSt n) n == one8) = true := by
  rw [stE_eqL, List.all_eq_true]
  intro y hy
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
  obtain ⟨m, hm, he⟩ := s8InvChk_sound _ _ _ s8InvChk_true n hn
  rw [memP_ofListP, List.contains_iff_mem] at hm
  have hs : (s8StL.find? fun m => mulP m n == oneP).isSome = true :=
    List.find?_isSome.mpr ⟨m, hm, by rw [he]; exact beq_self_eq_true _⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  rw [invSt_unpackM, hr, Option.getD_some, mul8_unpackM, ← oneP_eq, beq_mulP_one]
  exact List.find?_some (p := fun m => mulP m n == oneP) hr

theorem z8G_mem : (z8G.map code64R).all (fun g => s8StL.contains g) = true := by
  decide +kernel

theorem z8G_s8E : z8G.all (Std.HashSet.ofList s8E).contains = true := by
  rw [unpack_code64R_map z8G z8G_valid, List.all_map, List.all_eq_true]
  intro g hg
  have h1 : s8StL.contains g = true := List.all_eq_true.mp z8G_mem g hg
  rw [Function.comp_apply, Std.HashSet.contains_ofList, s8E_eq, List.contains_iff_mem]
  rw [List.contains_iff_mem, ← s8StL_eq] at h1
  exact List.mem_map_of_mem (List.mem_filter.mp h1).1

set_option maxHeartbeats 0 in
theorem s8_zB_true : zB = true := by
  simp only [zB, z8G_s8E, stE_invSt, Bool.and_true]
  simp only [Bool.or_comm (!_), stE_eqL, List.all_map, Function.comp_def, invSt_unpackM,
    ← oneP_eq, Std.HashSet.contains_ofList, subB, elemsOf_toF, elemsF_valid z8G_valid,
    contains_toLR, closedB, nodupB_toP, mul8_toF]
  decide +kernel

@[expose] noncomputable def s8DdP : List ℕ → List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun _ => [])
    (fun g _ ih seen => Bool.rec (g :: ih (g :: seen)) (ih seen) (seen.any (Nat.beq g)))

theorem s8DdP_cons (g : ℕ) (l seen : List ℕ) :
    s8DdP (g :: l) seen =
      if seen.any (Nat.beq g) = true then s8DdP l seen else g :: s8DdP l (g :: seen) := by
  cases h : seen.any (Nat.beq g)
  · exact (congrArg (fun b => Bool.rec (motive := fun _ => List ℕ) (g :: s8DdP l (g :: seen))
      (s8DdP l seen) b) h :)
  · exact (congrArg (fun b => Bool.rec (motive := fun _ => List ℕ) (g :: s8DdP l (g :: seen))
      (s8DdP l seen) b) h :)

@[expose] def s8StepF (x : ℕ) (st : NT ℕ × List ℕ × List ℕ) (g : ℕ) : NT ℕ × List ℕ × List ℕ :=
  let y := mulP g x
  if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)

@[expose] def s8RowF (gens : List ℕ) (st : NT ℕ × List ℕ × List ℕ) (x : ℕ) :
    NT ℕ × List ℕ × List ℕ :=
  (List.range gens.length).foldl (fun st i => s8StepF x st (gens.getD i oneP)) st

theorem s8StepF_self (x : ℕ) (st : NT ℕ × List ℕ × List ℕ) (g : ℕ) :
    memP (s8StepF x st g).1 (mulP g x) = true := by
  unfold s8StepF
  by_cases h : memP st.1 (mulP g x) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, memP_insP, beq_self_eq_true, Bool.true_or]

theorem s8StepF_mono (x : ℕ) (st : NT ℕ × List ℕ × List ℕ) (g z : ℕ) (hz : memP st.1 z = true) :
    memP (s8StepF x st g).1 z = true := by
  unfold s8StepF
  by_cases h : memP st.1 (mulP g x) = true
  · simp only [h, ↓reduceIte, hz]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, memP_insP, hz, Bool.or_true]

theorem s8StepF_of_mem (x : ℕ) (st : NT ℕ × List ℕ × List ℕ) (g : ℕ)
    (h : memP st.1 (mulP g x) = true) : s8StepF x st g = st := by
  unfold s8StepF
  simp only [h, ↓reduceIte]

theorem s8DdP_foldl (x : ℕ) : ∀ (l seen : List ℕ) (st : NT ℕ × List ℕ × List ℕ),
    (∀ g ∈ seen, memP st.1 (mulP g x) = true) →
      l.foldl (s8StepF x) st = (s8DdP l seen).foldl (s8StepF x) st
  | [], _, _, _ => rfl
  | g :: l, seen, st, h => by
    rw [s8DdP_cons]
    by_cases hg : seen.any (Nat.beq g) = true
    · simp only [hg, ↓reduceIte, List.foldl_cons]
      obtain ⟨g', hg', he⟩ := List.any_eq_true.mp hg
      rw [Nat.eq_of_beq_eq_true he, s8StepF_of_mem x st g' (h g' hg')]
      exact s8DdP_foldl x l seen st h
    · simp only [hg, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
      refine s8DdP_foldl x l (g :: seen) _ fun g' hg' => ?_
      rcases List.mem_cons.mp hg' with rfl | hg'
      · exact s8StepF_self x st g'
      · exact s8StepF_mono x st g _ (h g' hg')

theorem s8RowF_eq (gens : List ℕ) (st : NT ℕ × List ℕ × List ℕ) (x : ℕ) :
    s8RowF gens st x = gens.foldl (s8StepF x) st := by
  have hm : (List.range gens.length).map (fun i => gens.getD i oneP) = gens := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]
  conv_rhs => rw [← hm]
  rw [s8RowF, List.foldl_map]

theorem s8RowF_s8DdP (gens : List ℕ) : s8RowF (s8DdP gens []) = s8RowF gens := by
  funext st x
  rw [s8RowF_eq, s8RowF_eq, ← s8DdP_foldl x gens [] st fun _ h => absurd h List.not_mem_nil]

theorem bfsP_cons_eq (gens : List ℕ) (cap fuel : ℕ) (seen : NT ℕ) (acc : List ℕ) (a : ℕ)
    (fr : List ℕ) :
    bfsP gens cap (fuel + 1) seen acc (a :: fr) =
      if cap ≤ acc.length then acc else
        bfsP gens cap fuel ((a :: fr).foldl (s8RowF gens) (seen, acc, [])).1
          ((a :: fr).foldl (s8RowF gens) (seen, acc, [])).2.1
          ((a :: fr).foldl (s8RowF gens) (seen, acc, [])).2.2 := rfl

theorem bfsP_s8DdP (gens : List ℕ) (cap : ℕ) : ∀ (fuel : ℕ) (seen : NT ℕ) (acc fr : List ℕ),
    bfsP gens cap fuel seen acc fr = bfsP (s8DdP gens []) cap fuel seen acc fr
  | 0, _, _, _ => rfl
  | _ + 1, _, _, [] => rfl
  | fuel + 1, seen, acc, a :: fr => by
    rw [bfsP_cons_eq, bfsP_cons_eq, s8RowF_s8DdP]
    split
    · rfl
    · exact bfsP_s8DdP gens cap fuel _ _ _

theorem elemsP_s8DdP (gens : List ℕ) (cap : ℕ) : elemsP gens cap = elemsP (s8DdP gens []) cap :=
  bfsP_s8DdP gens cap 200 _ _ _

theorem elemsF_map_unpackM (L : List ℕ) (f : ℕ → ℕ) (cap : ℕ) :
    elemsF (L.map fun n => unpackM (f n)) cap =
      (elemsP (s8DdP (L.map fun n => code64R (unpackM (f n))) []) cap).map unpackM := by
  have hv : (L.map fun n => unpackM (f n)).all validB = true :=
    List.all_eq_true.mpr fun y hy => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hy
      exact validB_unpackM (f n)
  simp only [elemsF, hv, ↓reduceIte]
  rw [List.map_map, ← elemsP_s8DdP]
  rfl

set_option maxHeartbeats 0 in
theorem s8_nB_true : nB = true := by
  simp only [nB, stE_eqL, List.all_map, List.map_map, Function.comp_def, invSt_unpackM,
    elemsOf_toF, elemsF_valid n8G_valid, elemsF_valid z8G_valid, mul8_unpackM, ← oneP_eq,
    hs_contains_toLR', hs_contains_toLR, subB, closedB, nodupB_toP, contains_toLR,
    elemsF_map_unpackM]
  simp only [mul8_toF]
  decide +kernel

end CertificateChecks.KernelH13

end
