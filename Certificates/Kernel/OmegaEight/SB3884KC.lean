module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884IR

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

@[expose] noncomputable def kHi (a b : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (sMtRow (Nat.land a 511)) (Nat.mul 9 (Nat.land b 511))) 511

theorem kHi_key (a b y : ℕ) :
    (Nat.add (Nat.xor (Nat.land a 127) (Nat.land b 127)) (Nat.mul 128 y)) / 128 = y := by
  have h1 : a &&& 127 < 2 ^ 7 := Nat.and_lt_two_pow a (by decide)
  have h2 : b &&& 127 < 2 ^ 7 := Nat.and_lt_two_pow b (by decide)
  have h3 : (a &&& 127) ^^^ (b &&& 127) < 2 ^ 7 := Nat.xor_lt_two_pow h1 h2
  generalize hX : Nat.xor (Nat.land a 127) (Nat.land b 127) = X
  have h : X < 128 := by
    rw [← hX]
    exact h3
  have e : Nat.add X (Nat.mul 128 y) = X + 128 * y := rfl
  rw [e]
  omega

theorem mulK_div (c d : ℕ) : mulK c d / 128 = kHi (Nat.shiftRight c 7) (Nat.shiftRight d 7) := by
  unfold mulK sMulG
  simp only [strictN_eq']
  exact kHi_key _ _ _

@[expose] def k4Row (mul : ℕ → ℕ → ℕ) (hi : ℕ → ℕ → ℕ) (x : ℕ) (r : ℕ × List ℕ) : ℕ :=
  cond (hi r.1 (Nat.shiftRight x 7) == hi (Nat.shiftRight x 7) r.1)
    (r.2.filter fun c => mul c x == mul x c).length 0

@[expose] def k4Rows (mul : ℕ → ℕ → ℕ) (hi : ℕ → ℕ → ℕ) (R : List (ℕ × List ℕ)) (x : ℕ) : ℕ :=
  (R.map (k4Row mul hi x)).sum

theorem cInvC_rows {mul : ℕ → ℕ → ℕ} {hi : ℕ → ℕ → ℕ}
    (hhi : ∀ c d, mul c d / 128 = hi (Nat.shiftRight c 7) (Nat.shiftRight d 7))
    {R : List (ℕ × List ℕ)} (hR : ∀ r ∈ R, ∀ c ∈ r.2, Nat.shiftRight c 7 = r.1) (x : ℕ) :
    cInvC mul (R.map Prod.snd).flatten x = k4Rows mul hi R x := by
  unfold cInvC k4Rows
  induction R with
  | nil => rfl
  | cons r R ih =>
    rw [List.map_cons, List.flatten_cons, List.filter_append, List.length_append, List.map_cons,
      List.sum_cons, ih fun r' hr' => hR r' (List.mem_cons_of_mem _ hr')]
    congr 1
    unfold k4Row
    cases h : (hi r.1 (Nat.shiftRight x 7) == hi (Nat.shiftRight x 7) r.1)
    · rw [Bool.cond_false, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc hcx
      have e := congrArg (· / 128) (beq_iff_eq.1 hcx)
      simp only [hhi, hR r List.mem_cons_self c hc] at e
      rw [e, beq_self_eq_true] at h
      exact absurd h (by decide)
    · rfl

theorem sInvR_eq : sInvListLit = (sInvR.map Prod.snd).flatten := by decide +kernel

theorem sInvR_ok : ∀ r ∈ sInvR, ∀ c ∈ r.2, Nat.shiftRight c 7 = r.1 := by
  have h : (sInvR.all fun r => r.2.all fun c => Nat.shiftRight c 7 == r.1) = true := by
    decide +kernel
  simpa only [List.all_eq_true, beq_iff_eq] using h

theorem cInvC_K : cInvC mulK sInvListLit = k4Rows mulK kHi sInvR := by
  funext x
  rw [sInvR_eq, cInvC_rows mulK_div sInvR_ok]

@[expose] def kEntC (smul : ℕ → ℕ → ℕ) (N : ℕ) (cnt : ℕ → ℕ) (tab : ℕ → ℕ) (gens : List ℕ)
    (L : List (ℕ × ℕ × ℕ × ℕ)) (i : ℕ) : Bool :=
  let ws := L.map Prod.fst
  let e := L.getD i (0, 0, 0, 0)
  decide (e.1 < N) &&
    (i == 0 || (decide (e.2.2.1 < i) && decide (e.2.2.2 < gens.length) &&
      e.1 == smul (ws.getD e.2.2.1 0) (gens.getD e.2.2.2 0))) &&
    (gens.all fun g => ws.contains (smul e.1 g)) &&
    (e.1 == 0 || (decide (e.2.1 < N) && tab e.2.1 == e.1 && cnt e.1 != cnt e.2.1))

theorem kEnt_eqC (smul : ℕ → ℕ → ℕ) (N : ℕ) (I : List ℕ) (tab : ℕ → ℕ) (gens : List ℕ)
    (L : List (ℕ × ℕ × ℕ × ℕ)) : kEnt smul N I tab gens L = kEntC smul N (cInvC smul I) tab gens L :=
  rfl

@[expose] noncomputable def k5Lo (a d : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (sActRow (Nat.land a 511)) (Nat.mul 7 (Nat.land d 127))) 127

theorem mulK_lo (c d : ℕ) : mulK c d =
    Nat.xor (Nat.land c 127) (k5Lo (Nat.shiftRight c 7) d) +
      128 * kHi (Nat.shiftRight c 7) (Nat.shiftRight d 7) := by
  unfold mulK sMulG
  simp only [strictN_eq']
  rfl

@[expose] noncomputable def k5Row (x ex gx rx : ℕ) (r : ℕ × List ℕ) : ℕ :=
  cond (kHi r.1 gx == kHi gx r.1)
    (strictN (k5Lo r.1 x) fun w => (r.2.filter fun c => Nat.xor (Nat.land c 127) w ==
      Nat.xor ex (Nat.land (Nat.shiftRight rx (Nat.mul 7 (Nat.land c 127))) 127)).length) 0

@[expose] noncomputable def k5Rows (R : List (ℕ × List ℕ)) (x : ℕ) : ℕ :=
  strictN (Nat.shiftRight x 7) fun gx => strictN (sActRow (Nat.land gx 511)) fun rx =>
    (R.map (k5Row x (Nat.land x 127) gx rx)).sum

theorem k5Rows_eq {R : List (ℕ × List ℕ)} (hR : ∀ r ∈ R, ∀ c ∈ r.2, Nat.shiftRight c 7 = r.1)
    (x : ℕ) : k5Rows R x = k4Rows mulK kHi R x := by
  unfold k5Rows k4Rows
  simp only [strictN_eq']
  congr 1
  refine List.map_congr_left fun r hr => ?_
  unfold k5Row k4Row
  simp only [strictN_eq']
  cases h : (kHi r.1 (Nat.shiftRight x 7) == kHi (Nat.shiftRight x 7) r.1)
  · rfl
  · rw [Bool.cond_true, Bool.cond_true]
    congr 1
    refine List.filter_congr fun c hc => ?_
    have hc7 := hR r hr c hc
    rw [mulK_lo c x, mulK_lo x c, hc7, beq_iff_eq.1 h]
    have e : (Nat.xor (Nat.land c 127) (k5Lo r.1 x) +
        128 * kHi (Nat.shiftRight x 7) r.1 ==
        Nat.xor (Nat.land x 127) (k5Lo (Nat.shiftRight x 7) c) +
        128 * kHi (Nat.shiftRight x 7) r.1) =
        (Nat.xor (Nat.land c 127) (k5Lo r.1 x) ==
          Nat.xor (Nat.land x 127) (k5Lo (Nat.shiftRight x 7) c)) := by
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, Nat.add_right_cancel_iff]
    rw [e]
    try rfl

theorem cInvC_K5 : cInvC mulK sInvListLit = k5Rows sInvR := by
  funext x
  rw [cInvC_K, k5Rows_eq sInvR_ok]

@[expose] def k6Bits (es : List ℕ) : ℕ := es.foldr (fun e acc => acc ||| 1 <<< e) 0

theorem testBit_k6Bits (es : List ℕ) (i : ℕ) : (k6Bits es).testBit i = es.contains i := by
  induction es with
  | nil => simp [k6Bits]
  | cons e es ih =>
    simp only [k6Bits, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_lor, ih, Nat.one_shiftLeft, Nat.testBit_two_pow, List.contains_cons,
      Bool.or_comm]
    congr 1
    by_cases h : e = i
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem filter_length_k6Bits {n : ℕ} {es : List ℕ} (hnd : es.Nodup) (hlt : ∀ e ∈ es, e < n)
    (q : ℕ → Bool) : (es.filter q).length = ((List.range n).filter fun i =>
      (k6Bits es &&& k6Bits ((List.range n).filter q)).testBit i).length := by
  refine List.Perm.length_eq ((List.perm_ext_iff_of_nodup (hnd.filter _)
    (List.nodup_range.filter _)).2 fun i => ?_)
  simp only [List.mem_filter, List.mem_range, Nat.testBit_land, testBit_k6Bits,
    List.contains_iff_mem, Bool.and_eq_true]
  constructor
  · rintro ⟨hi, hq⟩
    exact ⟨hlt i hi, hi, hlt i hi, hq⟩
  · rintro ⟨_, hi, _, hq⟩
    exact ⟨hi, hq⟩

@[expose] def k6PcT : ℕ := 95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224

@[expose] def k6Pc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x =>
    Nat.land (Nat.shiftRight k6PcT (Nat.mul 4 (Nat.land x 255))) 15 + k6Pc k (Nat.shiftRight x 8)

theorem k6PcT_ok : ∀ b < 256,
    Nat.land (Nat.shiftRight k6PcT (Nat.mul 4 b)) 15 = ((List.range 8).filter b.testBit).length := by
  decide +kernel

theorem k6Pc_eq (k x : ℕ) : k6Pc k x = ((List.range (8 * k)).filter x.testBit).length := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [k6Pc, ih, Nat.mul_succ, Nat.add_comm (8 * k) 8, List.range_add, List.filter_append,
      List.length_append, List.filter_map, List.length_map]
    have hx : Nat.land x 255 < 256 := lt_of_lt_of_eq (Nat.and_lt_two_pow x (n := 8) (by decide)) rfl
    rw [k6PcT_ok _ hx]
    congr 2
    · refine List.filter_congr fun i hi => ?_
      rw [List.mem_range] at hi
      change (x &&& 255).testBit i = x.testBit i
      have h255 : (255 : ℕ).testBit i = true := by interval_cases i <;> rfl
      rw [Nat.testBit_land, h255, Bool.and_true]
    · refine List.filter_congr fun i _ => ?_
      change (x >>> 8).testBit i = x.testBit (8 + i)
      rw [Nat.testBit_shiftRight]

@[expose] def k6Pre (rx : ℕ) : ℕ :=
  k6Bits ((List.range 128).map fun e =>
    128 * Nat.xor e (Nat.land (Nat.shiftRight rx (Nat.mul 7 e)) 127) + e)

theorem testBit_k6Pre (rx v : ℕ) {i : ℕ} (hi : i < 128) : (k6Pre rx >>> (128 * v)).testBit i =
    (Nat.xor i (Nat.land (Nat.shiftRight rx (Nat.mul 7 i)) 127) == v) := by
  rw [Nat.testBit_shiftRight, k6Pre, testBit_k6Bits, Bool.eq_iff_iff, List.contains_iff_mem,
    List.mem_map, beq_iff_eq]
  constructor
  · rintro ⟨e, he, h⟩
    rw [List.mem_range] at he
    obtain rfl : e = i := by omega
    omega
  · intro h
    exact ⟨i, List.mem_range.2 hi, by rw [h]⟩

theorem k6_xor (a b c d : ℕ) : (a ^^^ b == c ^^^ d) = (a ^^^ d == c ^^^ b) := by
  have key : ∀ p q r s : ℕ, p ^^^ q = r ^^^ s → p ^^^ s = r ^^^ q := by
    intro p q r s h
    have hp : p = r ^^^ s ^^^ q := by rw [← h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hp, Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm q s, ← Nat.xor_assoc s, Nat.xor_self,
      Nat.zero_xor]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨key a b c d, key a d c b⟩

theorem k6_count {cs : List ℕ} (hnd : (cs.map fun c => Nat.land c 127).Nodup) (rx ex w : ℕ) :
    k6Pc 16 (Nat.land (k6Bits (cs.map fun c => Nat.land c 127))
      (Nat.shiftRight (k6Pre rx) (Nat.mul 128 (Nat.xor ex w)))) =
    (cs.filter fun c => Nat.xor (Nat.land c 127) w ==
      Nat.xor ex (Nat.land (Nat.shiftRight rx (Nat.mul 7 (Nat.land c 127))) 127)).length := by
  have hlt : ∀ e ∈ cs.map (fun c => Nat.land c 127), e < 128 := by
    intro e he
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 he
    exact lt_of_lt_of_eq (Nat.and_lt_two_pow c (n := 7) (by decide)) rfl
  let q : ℕ → Bool := fun e =>
    Nat.xor e w == Nat.xor ex (Nat.land (Nat.shiftRight rx (Nat.mul 7 e)) 127)
  have e1 : ((cs.map fun c => Nat.land c 127).filter q).length = (cs.filter fun c =>
      Nat.xor (Nat.land c 127) w ==
        Nat.xor ex (Nat.land (Nat.shiftRight rx (Nat.mul 7 (Nat.land c 127))) 127)).length := by
    rw [List.filter_map, List.length_map]
    rfl
  have h128 : (8 : ℕ) * 16 = 128 := rfl
  rw [← e1, filter_length_k6Bits hnd hlt q, k6Pc_eq, h128]
  congr 1
  refine List.filter_congr fun i hi => ?_
  rw [List.mem_range] at hi
  change (k6Bits _ &&& (k6Pre rx >>> (128 * (ex ^^^ w)))).testBit i =
    (k6Bits _ &&& k6Bits _).testBit i
  rw [Nat.testBit_land, Nat.testBit_land, testBit_k6Pre rx _ hi, testBit_k6Bits,
    testBit_k6Bits]
  congr 1
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_filter, List.mem_range]
  constructor
  · intro h
    exact ⟨hi, (k6_xor i w ex (Nat.land (Nat.shiftRight rx (Nat.mul 7 i)) 127)).trans h⟩
  · rintro ⟨-, h⟩
    exact (k6_xor i w ex (Nat.land (Nat.shiftRight rx (Nat.mul 7 i)) 127)).symm.trans h

@[expose] def sInvM : List (ℕ × ℕ) :=
  [(0, 340282366920938463463374607431768211454), (1, 320265757102059730302193679870744006415),
    (2, 4003321963775746628980877734491390723), (3, 16013287855102986515272449382422872835),
    (4, 181483929024500513838524643395878588689), (5, 170808403787765189493996914721196933377),
    (6, 42702100946941297373553483809927790849), (7, 53377626183676621721553540780837126465),
    (8, 22685491128062564230891640495451214097), (9, 21351050473470648686812911991382933761),
    (10, 44036541601533212918789655079405297953), (11, 42702100946941297373553483809927790849),
    (12, 136112946768375385389039191787449194905), (13, 128106302840823892121094492466811832585),
    (14, 2668881309183831085914911650156183809), (15, 5337762618367662171757483127474290945),
    (16, 6672203272959577714968129557485651205), (17, 13344406545919155429574558250780919045),
    (18, 12009965891327239886942633203474172169), (19, 8006643927551493258178775987497011465),
    (20, 85404201893882594747034627447017505025), (21, 96079727130617919092719798887108387105),
    (22, 32026575710205973039442740023929176449), (23, 21351050473470648686812911991382933761),
    (24, 86738642548474510294585684247313465665), (25, 85404201893882594747034627447017505025),
    (26, 172142844442357105046177742583129801089), (27, 170808403787765189493996914721196933377),
    (28, 5337762618367662171757483127474290945), (29, 2668881309183831085914911650156183809),
    (30, 192159454261235838181316207922446403849), (31, 200166098188787331445788578946856085865),
    (32, 47536897497490556114477619609), (36, 22685491165035706737548331370434072849),
    (40, 181483928987527371349084913652349341969), (44, 204169420105026180569466161905511537049),
    (50, 12009965933271561218023753103664810249), (54, 32026575742829334059536619209396158849),
    (58, 172142844409733744010892427105203749249), (62, 192159454219291516869766934683988855049),
    (64, 203371895524352202572768583375069905049), (65, 191408842846449131823466185046389424137),
    (68, 23305788061115467401646448005222008849), (69, 21934859351638086965140707561649473537),
    (72, 180863632091447610667837088614347999249), (73, 170224594909597751215673075193768052737),
    (76, 797524628210875516237759734765060249), (77, 750611414786706358495998090808393737),
    (82, 12713664092689777097462792983466250249), (83, 750611414786706358495998090808393737),
    (86, 171595523619075131660217618309802629249), (87, 170224594909597751215673075193768052737),
    (90, 32573896533487946425343523654691461249), (91, 21934859351638086965140707561649473537),
    (94, 191455756059873300970872343254323466249), (95, 191408842846449131823466185046389424137),
    (96, 797524675376396657800902559553028249), (100, 180863632054763316446621310861735135249),
    (104, 23305788097799761639944681432839391249),
    (108, 203371895477186681409242283253847556249),
    (114, 12713664134306413418221293090427146249),
    (118, 171595523586706636744072118226610821249),
    (122, 32573896565856441326416268730526341249),
    (126, 191455756018256664669493099585392906249),
    (128, 19938421129838451232624370919124500495), (129, 78188689040281913356643111251476495),
    (130, 15966374641678817367909525071214676995), (131, 4050235177199915776348888386490862595),
    (140, 7975368451935380493265921162698817545), (141, 31275475616112765558830039549607945),
    (142, 5327337459828957916789357264092268545), (143, 2679306467722535340886993556375865345),
    (144, 13318343649572394792150711411220810245), (145, 6698266169306338352394802141929802245),
    (146, 11994328153519183504486629652807681545), (147, 8022281665359549640633084091233076745),
    (156, 2679306467722535340886993556375865345), (157, 5327337459828957916789357264092268545),
    (158, 31275475616112765558830039549607945), (159, 7975368451935380493265921162698817545),
    (192, 139568947908869158628370596433871503465),
    (193, 127605895230966087882526962825975300105),
    (198, 85237399357263326667514943311622703105), (199, 86608328066740707107452321325092710465),
    (202, 95876436539113186120813793538539538465), (203, 85237399357263326667514943311622703105),
    (204, 127605895230966087882526962825975300105),
    (205, 127652808444390257029919557458465939465),
    (210, 12463460287760874978166736172802400265), (211, 500407609857804239213504855587946505),
    (212, 42868903483560565453077123988160251905), (213, 44239832193037945890717701238069676065),
    (216, 53507940665410424908672774978637670465), (217, 42868903483560565453077123988160251905),
    (222, 500407609857804239213504855587946505), (223, 547320823281973393496501778760335465),
    (272, 113870524878207751990711636412806638165),
    (273, 107172258708901413632870128221390768645),
    (276, 90564736817092284585419073489568565265), (277, 85237399357263326667514943311622703105),
    (282, 1370928709477380435390967529718941697), (283, 5327337459828957916789357264092268545),
    (286, 21934859351638086965140707561649473537), (287, 27262196811467044886476475309492807745),
    (304, 5426301633866775261186918417), (308, 23305788055689165766516263442256005137),
    (314, 1370928714265293642858777438218356737), (318, 21934859346850173759902443480338139137),
    (320, 68853998012398568197931102570344664115), (321, 64803762835198652418288758850205780995),
    (324, 45548209951283100795078890458389710865), (325, 42868903483560565453077123988160251905),
    (330, 1370928709477380435390967529718941697), (331, 2679306467722535340886993556375865345),
    (334, 21934859351638086965140707561649473537), (335, 24614165819360622308277310838215821345),
    (352, 5426301633866775261186918417), (356, 23305788055689165766516263442256005137),
    (362, 1370928714265293642858777438218356737), (366, 21934859346850173759902443480338139137),
    (402, 5327337459828957916789357264092268545), (403, 1370928709477380435390967529718941697),
    (406, 175551932369426709134712042178050803745),
    (407, 170224594909597751215673075193768052737),
    (408, 213093498393158316668964676530046896645),
    (409, 219791764562464655032548186630364224165),
    (412, 42868903483560565453077123988160251905), (413, 48196240943389523379020056838568155265),
    (435, 125101942358892149765187809845444737), (439, 171470421676716239501163782104896503937),
    (441, 1412629382927086868981239155801460737), (445, 170182894236148044800385433544241975297),
    (450, 255461994266861077883258945805786811395),
    (451, 259512229444060993673236892961948318915),
    (454, 85237399357263326667514943311622703105), (455, 87916705824985862017555512454314203265),
    (456, 2679306467722535340886993556375865345), (457, 1370928709477380435390967529718941697),
    (460, 172903901377320286561106479233894983745),
    (461, 170224594909597751215673075193768052737), (483, 1412629382927086868981239155801460737),
    (487, 170182894236148044800385433544241975297), (489, 125101942358892149765187809845444737),
    (493, 171470421676716239501163782104896503937)]

set_option maxHeartbeats 0 in
theorem sInvM_eq : sInvM = sInvR.map fun r => (r.1, k6Bits (r.2.map fun c => Nat.land c 127)) := by
  decide +kernel

theorem sInvR_nd : ∀ r ∈ sInvR, (r.2.map fun c => Nat.land c 127).Nodup := by
  have h : (sInvR.all fun r => ((r.2.map fun c => Nat.land c 127).zip
      (r.2.map fun c => Nat.land c 127).tail).all fun p => decide (p.1 < p.2)) = true := by
    decide +kernel
  intro r hr
  have hs := List.all_eq_true.1 (List.all_eq_true.1 h r hr)
  exact (List.isChain_iff_pairwise.1 (chain_of_zip_tail' fun p hp =>
    of_decide_eq_true (hs p hp))).imp ne_of_lt

@[expose] noncomputable def k6RowM (x ex gx pre : ℕ) (r : ℕ × ℕ) : ℕ :=
  cond (kHi r.1 gx == kHi gx r.1)
    (strictN (k5Lo r.1 x) fun w =>
      k6Pc 16 (Nat.land r.2 (Nat.shiftRight pre (Nat.mul 128 (Nat.xor ex w))))) 0

@[expose] noncomputable def k6Rows (M : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  strictN (Nat.shiftRight x 7) fun gx => strictN (sActRow (Nat.land gx 511)) fun rx =>
    strictN (k6Pre rx) fun pre => (M.map (k6RowM x (Nat.land x 127) gx pre)).sum

theorem k6Rows_eq (x : ℕ) : k6Rows sInvM x = k5Rows sInvR x := by
  unfold k6Rows k5Rows
  simp only [strictN_eq']
  rw [sInvM_eq, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  obtain ⟨g, cs⟩ := r
  simp only [Function.comp_apply]
  unfold k6RowM k5Row
  simp only [strictN_eq']
  cases h : (kHi g (Nat.shiftRight x 7) == kHi (Nat.shiftRight x 7) g)
  · rw [Bool.cond_false, Bool.cond_false]
  · rw [Bool.cond_true, Bool.cond_true, k6_count (sInvR_nd _ hr)]

theorem kDataF_ofR6 {tab : ℕ → ℕ} {gens : List ℕ} {L : List (ℕ × ℕ × ℕ × ℕ)}
    (hL : L.length = 64)
    (h0 : (L.head? == some (0, 0, 0, 0) && (L.map Prod.fst).Nodup &&
      (gens.all fun g => decide (g < 65536))) = true)
    (hb : ∀ s < 8, (List.range' (8 * s) 8).all
      (kEntC mulK 65536 (k6Rows sInvM) tab gens L) = true) :
    (kDataF mulK 65536 sInvListLit tab gens L && L.length == 64) = true :=
  kDataF_of hL h0 fun s hs => by
    have hk : k6Rows sInvM = k5Rows sInvR := funext k6Rows_eq
    rw [kEnt_eqC, cInvC_K5, ← hk]
    exact hb s hs

end CertificateChecks.KernelO8.SB3884

end
