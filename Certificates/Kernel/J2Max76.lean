module

public import Certificates.Data.Kernel.J2Max76
import Certificates.Kernel.J2Max76.Fast
import CFSG.Certificates.Kernel.J2Max76FastSound
import CFSG.Certificates.Kernel.J2Max76PackSound
import CFSG.Certificates.Kernel.MonsterB.NatBfsLSound
import CFSG.Certificates.Kernel.MonsterB.BfsReplayEqSound

public section

namespace CertificateChecks.J2Max76

open Certificates.K76J2Max Certificates.G2ThreeMax CFSG.Monster.B.TwoA.Census CFSG.KC.Bfs
  CFSG.KC.J2Max76 CertificateChecks.KernelJ2Max76

theorem orbitSearch_eq_L (act : ℕ → ℕ → ℕ) (nh N : ℕ) :
    orbitSearch act nh N = orbitSearchL act nh N := by
  unfold orbitSearch orbitSearchL
  rw [natBfs_eq_natBfsL_fun]

theorem repOK_eq_L (c : NatCert) (hp : Array (Array ℕ)) (r : ℕ) :
    repOK c hp r = repOKL c hp r := by
  unfold repOK repOKL
  rw [natBfs_eq_natBfsL_fun]

private theorem tabs_size : nTabsL.size = 3 := by
  have h := tabs_pin
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem tabs_pinT : pinT nTabsP 9 280 (nTabsL.toList.map Array.toList) = true := by
  have h := tabs_pin
  rw [Bool.and_eq_true] at h
  exact h.2

private theorem tab_eq : tabOf orbLit = tabR orbEdgesP :=
  tabOf_eq_R orbLit orbEdgesP (certPin_edges _ _ _ _ _ _ _ _ orb_pin)

private theorem orbLit_size : orbLit.pts.size = 280 := certPin_size _ _ _ _ _ _ _ _ orb_pin

private theorem rp_eq (w : List ℕ) (rp : Array ℕ) (h : (permL (tabR orbEdgesP) 280 w == rp.toList) = true) :
    permArr orbLit w = rp := by
  apply Array.toList_inj.mp
  rw [permArr_toList, tab_eq, orbLit_size]
  exact beq_iff_eq.mp h

private theorem natBfsL_of_pin {act : ℕ → ℕ → ℕ} {m : ℕ} {valid : ℕ → Bool} {root n W PKp PKe PKpar
    PKlab : ℕ} {c : NatCert} (hp : certPin c n W m PKp PKe PKpar PKlab = true)
    (hok : natCertOK act m valid root c = true)
    (hrep : replayTOK (rdT PKe 9 m) (lane PKpar 9) (lane PKlab 9) m n = true)
    (hpl : (c.par.size == n && c.lab.size == n && lane PKpar 9 0 == 0 && lane PKlab 9 0 == 0) =
      true) {fuel : ℕ} (hfuel : n ≤ fuel) :
    natBfsL act m root fuel = c := by
  have hs := certPin_size _ _ _ _ _ _ _ _ hp
  unfold certPin at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp hpl
  obtain ⟨⟨⟨⟨⟨-, hes⟩, -⟩, hpe⟩, hpar⟩, hlab⟩ := hp
  obtain ⟨⟨⟨hps, hls⟩, hp0⟩, hl0⟩ := hpl
  have eE : (fun i k => (c.edges[i]!)[k]!) = rdT PKe 9 m :=
    funext fun i => funext fun k => pinT_arr PKe 9 m c.edges hpe i k
  have eP : (fun j => c.par[j]!) = lane PKpar 9 :=
    funext fun j => by rw [arr_getD, pin1_lane 9 _ _ hpar]; rfl
  have eL : (fun j => c.lab[j]!) = lane PKlab 9 :=
    funext fun j => by rw [arr_getD, pin1_lane 9 _ _ hlab]; rfl
  rw [← natBfs_eq_natBfsL]
  rw [← eE, ← eP, ← eL, ← hs] at hrep
  exact natBfs_eq_of_replayT hok hrep (by omega) (by rw [hes, hs]) (by rw [hps, hs])
    (by rw [hls, hs]) ((congrFun eP 0).trans hp0) ((congrFun eL 0).trans hl0)

private theorem j2RepOKL_of (r : ℕ) (w : List ℕ) (rp : Array ℕ) (c₃ : NatCert)
    (PKrp PKp PKe PKpar PKlab : ℕ) (hw : (pathWord orbLit 280 r == w) = true)
    (hrp : (permL (tabR orbEdgesP) 280 w == rp.toList) = true) (hr : pin1 9 rp.toList PKrp = true)
    (hc : certPin c₃ 280 9 4 PKp PKe PKpar PKlab = true)
    (hrep : replayTOK (rdT PKe 9 4) (lane PKpar 9) (lane PKlab 9) 4 280 = true)
    (hpl : (c₃.par.size == 280 && c₃.lab.size == 280 && lane PKpar 9 0 == 0 &&
      lane PKlab 9 0 == 0) = true)
    (h : repLitP orbLit nTabsP r w PKrp PKp PKe PKpar PKlab c₃.pts.toList = true) :
    repOKL orbLit nTabsL r = true := by
  have hl := repLitOK_of_P _ _ _ _ _ _ _ _ _ _ _ _ tabs_size tabs_pinT hr hc h
  have hok : natCertOK (repAct nTabsL rp) 4 (fun u => decide (u < 280)) 0 c₃ = true := by
    have hl' := hl
    unfold repLitOK at hl'
    simp only [Bool.and_eq_true] at hl'
    exact hl'.1.2
  exact repOKL_of _ _ _ _ _ _ (beq_iff_eq.mp hw) (rp_eq _ _ hrp) (natBfsL_of_pin hc hok hrep hpl le_rfl) hl

private theorem repLitP_of_Q {c : NatCert} {PKh r : ℕ} {w : List ℕ} {PKrp PKp PKe PKpar PKlab : ℕ}
    {L : List ℕ} (h : repLitQ c PKh r w PKrp PKp PKe PKpar PKlab L = true) :
    repLitP c PKh r w PKrp PKp PKe PKpar PKlab L = true := by
  unfold repLitQ natCertQ at h
  unfold repLitP natCertP natCertR
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hw, ha⟩, ⟨h0, hr⟩, hall⟩, hs⟩ := h
  refine ⟨⟨⟨hw, ha⟩, ⟨⟨h0, hr⟩, hall⟩, ?_⟩, hs⟩
  rw [beq_iff_eq] at hs
  rw [hs]
  exact decide_eq_true List.pairwise_lt_range

private theorem rep1 : repOKL orbLit nTabsL 1 = true :=
  j2RepOKL_of _ _ _ _ _ _ _ _ _ w1_lit rp1_lit rp1_pin c1_pin c1_replay c1_pl (repLitP_of_Q rep1_ok)

private theorem rep15 : repOKL orbLit nTabsL 15 = true :=
  j2RepOKL_of _ _ _ _ _ _ _ _ _ w15_lit rp15_lit rp15_pin c15_pin c15_replay c15_pl
    (repLitP_of_Q rep15_ok)

private theorem rep18 : repOKL orbLit nTabsL 18 = true :=
  j2RepOKL_of _ _ _ _ _ _ _ _ _ w18_lit rp18_lit rp18_pin c18_pin c18_replay c18_pl
    (repLitP_of_Q rep18_ok)

private theorem reps_ok : (orbsLit.all fun t => t.1 == 0 || repOKL orbLit nTabsL t.1) = true := by
  rw [orbsLit.eq_1]
  simp only [List.all_cons, List.all_nil, rep1, rep15, rep18, Bool.or_true, Bool.and_true,
    beq_self_eq_true, Bool.true_or]

private theorem orbs_B : orbitSearchL (hR nTabsP) 3 280 =
    orbitSearchB (lookB orbsLit fun i => natBfsL (hR nTabsP) 3 i 280) 280 := by
  have ok : ∀ (r n PKp PKe PKpar PKlab : ℕ) (c : NatCert),
      certPin c n 9 3 PKp PKe PKpar PKlab = true →
      natCertP (hR nTabsP) 3 (fun u => decide (u < 280)) r n 9 3 PKp PKe PKpar PKlab c.pts.toList =
        true →
      natCertOK (hR nTabsP) 3 (fun u => decide (u < 280)) r c = true :=
    fun r n PKp PKe PKpar PKlab c hp h => (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ hp).trans h
  have hB : (fun i => natBfsL (hR nTabsP) 3 i 280) =
      lookB orbsLit fun i => natBfsL (hR nTabsP) 3 i 280 := by
    funext i
    unfold lookB
    rw [orbsLit.eq_1]
    by_cases h0 : i = 0
    · subst h0
      exact natBfsL_of_pin o0_pin (ok _ _ _ _ _ _ _ o0_pin o0_ok) o0_replay o0_pl (by omega)
    by_cases h1 : i = 1
    · subst h1
      exact natBfsL_of_pin o1_pin (ok _ _ _ _ _ _ _ o1_pin o1_ok) o1_replay o1_pl (by omega)
    by_cases h15 : i = 15
    · subst h15
      exact natBfsL_of_pin o15_pin (ok _ _ _ _ _ _ _ o15_pin o15_ok) o15_replay o15_pl (by omega)
    by_cases h18 : i = 18
    · subst h18
      exact natBfsL_of_pin o18_pin (ok _ _ _ _ _ _ _ o18_pin o18_ok) o18_replay o18_pl (by omega)
    simp only [List.lookup, beq_false_of_ne h0, beq_false_of_ne h1, beq_false_of_ne h15,
      beq_false_of_ne h18, Option.getD]
  exact congrArg (orbitSearchB · 280) hB

private theorem orbs_ok : okOrbs nTabsL 280 orbsLit = true := by
  refine okOrbs_of _ _ _ (fun t ht => ?_) orbs_cover
  rw [hAct_eq_R _ _ tabs_pinT, tabs_size]
  rw [orbsLit.eq_1] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ o0_pin).trans o0_ok
  · exact (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ o1_pin).trans o1_ok
  · exact (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ o15_pin).trans o15_ok
  · exact (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ o18_pin).trans o18_ok

private theorem ltFromB_pw (l : List ℕ) (p : ℕ) (h : ltFromB l p = true) :
    (p :: l).Pairwise (· < ·) := by
  induction l generalizing p with
  | nil => exact List.pairwise_singleton _ _
  | cons a l ih =>
    change (Nat.blt p a && ltFromB l a) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    have h2 := ih a h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, h2⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 ((List.pairwise_cons.1 h2).1 x hx)

private theorem ltSortedB_pw (l : List ℕ) (h : ltSortedB l = true) : l.Pairwise (· < ·) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons a t => exact ltFromB_pw t a h

private theorem natCertR_of_A {act A : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root n : ℕ}
    {P : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {R par lab : ℕ → ℕ} {Q : ℕ → Bool} {L : List ℕ}
    (hA : ∀ i k, Q i = true → valid (P i) = true → k < ngen → act k (P i) = A k i)
    (h : natCertA A ngen valid root n P E R par lab Q L = true) :
    natCertR act ngen valid root n P E R par lab L = true := by
  unfold natCertA at h
  unfold natCertR
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h ⊢
  obtain ⟨⟨⟨h0, hr⟩, hall⟩, hL⟩ := h
  refine ⟨⟨⟨h0, hr⟩, fun i hi => ?_⟩, decide_eq_true (ltSortedB_pw _ hL)⟩
  have hp := hall i hi
  unfold natPointA at hp
  unfold natPointR
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hp ⊢
  obtain ⟨⟨⟨⟨hq, hv⟩, hR⟩, he⟩, hpar⟩ := hp
  refine ⟨⟨⟨hv, hR⟩, fun k hk => ?_⟩, ?_⟩
  · rw [hA i k hq hv hk]
    exact he k hk
  · by_cases hi0 : i = 0
    · subst hi0
      rfl
    · have hb : (i == 0) = false := by simpa using hi0
      rw [hb, Bool.false_or] at hpar ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpar ⊢
      obtain ⟨⟨hpi, hli⟩, he2⟩ := hpar
      have hq2 := hall (par i) (by omega)
      unfold natPointA at hq2
      simp only [Bool.and_eq_true] at hq2
      refine ⟨⟨hpi, hli⟩, ?_⟩
      rw [hA _ _ hq2.1.1.1.1 hq2.1.1.1.2 hli]
      exact he2

private theorem testBit_foldl_if (p : ℕ → Bool) (g : ℕ → ℕ) (L : List ℕ) (acc b : ℕ) :
    (L.foldl (fun a i => if p i then a ||| 2 ^ g i else a) acc).testBit b = true ↔
      acc.testBit b = true ∨ ∃ i ∈ L, p i = true ∧ g i = b := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih]
    cases hx : p x
    · simp only [Bool.false_eq_true, ite_false, List.mem_cons]
      grind
    · simp only [ite_true, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
        List.mem_cons]
      grind

private theorem orLanesW_succ (f : ℕ → ℕ) (c x acc : ℕ) :
    orLanesW f (c + 1) x acc = orLanesW f c (x >>> 9) (acc ||| 2 ^ f (x &&& 511)) := by
  change forceJ (Nat.shiftRight x (nat_lit 9)) (fun y => forceJ (Nat.lor acc
    (Nat.shiftLeft (nat_lit 1) (f (Nat.land x (nat_lit 511))))) fun a => orLanesW f c y a) = _
  rw [forceJ_eq, forceJ_eq, ← Nat.one_shiftLeft]
  rfl

private theorem testBit_orLanesW (f : ℕ → ℕ) (c x acc b : ℕ) :
    (orLanesW f c x acc).testBit b = true ↔
      acc.testBit b = true ∨ ∃ j < c, f (x >>> (9 * j) &&& 511) = b := by
  induction c generalizing x acc with
  | zero =>
    change acc.testBit b = true ↔ _
    simp
  | succ c ih =>
    rw [orLanesW_succ, ih, Nat.testBit_or, Nat.testBit_two_pow, Nat.exists_lt_succ_left]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Nat.mul_zero, Nat.shiftRight_zero,
      ← Nat.shiftRight_add, Nat.mul_succ]
    grind

private theorem testBit_lt {n N e : ℕ} (hn : n < 2 ^ N) (he : n.testBit e = true) : e < N := by
  by_contra hc
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega)
    (Nat.le_of_not_lt hc)))] at he
  exact Bool.false_ne_true he

private theorem act_eq_imgMem (G M : ℕ) (hG : pinT G 9 315 (gensArr.toList.map Array.toList) = true)
    (i k n : ℕ) (hq : (n == memCode M i) = true) (hv : decide (n < 2 ^ 315) = true) :
    act k n = imgMem G M k i := by
  rw [beq_iff_eq] at hq
  rw [decide_eq_true_eq] at hv
  have hn : ∀ e, n.testBit e = true ↔ ∃ j < 45, (lane M 405 i >>> (9 * j) &&& 511) = e := by
    intro e
    rw [hq]
    unfold memCode
    rw [testBit_orLanesW]
    simp
  apply Nat.eq_of_testBit_eq
  intro b
  apply Bool.eq_iff_iff.mpr
  unfold act imgSet imgMem
  rw [testBit_foldl_if, testBit_orLanesW]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_range]
  constructor
  · rintro ⟨e, -, he, rfl⟩
    obtain ⟨j, hj, rfl⟩ := (hn e).1 he
    exact ⟨j, hj, (pinT_arr G 9 315 gensArr hG k _).symm⟩
  · rintro ⟨j, hj, rfl⟩
    have he := (hn _).2 ⟨j, hj, rfl⟩
    refine ⟨_, ?_, he, pinT_arr G 9 315 gensArr hG k _⟩
    exact testBit_lt hv he

private theorem orb_ok : natCertP act 5 (fun u => decide (u < 2 ^ 315)) rootLit 280 315 5
    orbPtsP orbEdgesP orbParP orbLabP orbLit.pts.toList = true :=
  natCertR_of_A (fun i k hq hv _ => act_eq_imgMem _ _ gens_pinM i k _ hq hv) orb_okA

theorem check_true : check () = true := by
  have hroot : root () = rootLit := beq_iff_eq.mp root_lit
  have hact : act = actK gensL := act_eq_actK gensL gens_lit
  have hok : natCertOK (actK gensL) 5 (fun u => decide (u < 2 ^ 315)) rootLit orbLit = true :=
    (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ orb_pin).trans (by rw [← hact]; exact orb_ok)
  have e0 : orbitCert () = natBfsL act 5 (root ()) 280 := natBfs_eq_natBfsL _ _ _ _
  rw [hact, hroot, natBfsL_of_pin orb_pin hok orb_replay orb_pl le_rfl] at e0
  have ht : nTabs orbLit = nTabsL := arrEq _ _ (by
    rw [nTabs_toList, tab_eq, orbLit_size]
    exact tabs_lit)
  have ho : orbitSearch (hAct nTabsL) 3 280 = orbsLit := by
    rw [orbitSearch_eq_L, hAct_eq_R _ _ tabs_pinT, orbs_B]
    exact orbsEqB_eq _ _ orbs_lit
  have hc : check () = (natCertOK (actK gensL) 5 (fun u => decide (u < 2 ^ 315)) rootLit orbLit &&
      orbLit.pts.size == 280 && (List.range 3).all (fun s => tabOf orbLit (s + 2) 0 == 0) &&
      okOrbs nTabsL 280 orbsLit &&
      orbsLit.all fun t => t.1 == 0 || repOKL orbLit nTabsL t.1) := by
    unfold check
    simp only [e0, ht, ho, repOK_eq_L, hact, hroot]
  rw [hc, hok, orb_size, orb_fix, orbs_ok, reps_ok]
  rfl

end CertificateChecks.J2Max76
