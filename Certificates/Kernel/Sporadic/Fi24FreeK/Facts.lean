module

public import Certificates.Kernel.Sporadic.Fi24FreeK.Checks
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Facts
public import CFSG.Certificates.Kernel.Spor.Fi24FreeKSound

public section

namespace CFSG.KD.Fi24FreeK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24FreeK CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt CFSG.KS.Fi24Kit
  CFSG.KS.Fi24ThreeO CFSG.KS.Fi24FreeK CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO
  CFSG.KC.Benes

theorem invC_append : ∀ (u v : List Nat), invC (u ++ v) = invC v ++ invC u
  | [], v => by rw [List.nil_append]; exact (List.append_nil _).symm
  | c :: u, v => by
    rw [List.cons_append, invC_cons, invC_append u v, invC_cons, List.append_assoc]

theorem invC_invC : ∀ {W : List Nat}, (∀ c ∈ W, c < 26) → invC (invC W) = W
  | [], _ => rfl
  | c :: W, h => by
    have hc := h c List.mem_cons_self
    rw [invC_cons, invC_append, invC_invC (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))]
    change invC [nIf(Nat.beq c (nat_lit 26), nat_lit 26, Nat.xor c (nat_lit 1))] ++ W = c :: W
    rw [invC_cons]
    interval_cases c <;> rfl

theorem cP_invC' {W : List Nat} (hW : ∀ c ∈ W, c < 26) (x : Nat) :
    cP NW NT W (cP NW NT (invC W) x) = x := by
  have h := cP_invC (invC_lt hW) x
  rwa [invC_invC hW] at h

structure FrameN : Prop where
  c0w : cP NW NT wc0 0 = c0
  c1w : cP NW NT wc1 0 = c1
  m1 : clsK OL NT 0 305530 = 73618
  m2 : clsK OL NT c0 c1 = 65697
  cm : clsK OL NT 0 c0 = c0 ∧ clsK OL NT 0 c1 = c1 ∧
    clsK OL NT 305530 c0 = c0 ∧ clsK OL NT 305530 c1 = c1
  conj : ∀ b ∈ base, cP NW NT (G1 ++ [2]) b =
    clsK OL NT 0 (clsK OL NT 305530 (clsK OL NT c0 (clsK OL NT c1 (cP NW NT G1 b))))
  efix : ∀ j < 6, ∀ p ∈ [0, 305530, c0, c1], cP NW NT (nthD [] eps j) p = p
  rl_len : rl.length = 26
  rels : ∀ i < 26, ∀ b ∈ base, cP NW NT (epsL (nthD [] rl i)) b = b
  mv : cP NW NT (nthD [] eps 0) mv ≠ mv

theorem base_len : base.length = 6 := rfl

theorem cj_all : ∀ b < 6, cj b = true := by
  intro b hb
  interval_cases b
  exacts [Ck.cj0, Ck.cj1, Ck.cj2, Ck.cj3, Ck.cj4, Ck.cj5]

theorem rel_all : ∀ i < 26, rel i = true := by
  intro i hi
  interval_cases i
  exacts [Ck.rel0, Ck.rel1, Ck.rel2, Ck.rel3, Ck.rel4, Ck.rel5, Ck.rel6, Ck.rel7, Ck.rel8,
    Ck.rel9, Ck.rel10, Ck.rel11, Ck.rel12, Ck.rel13, Ck.rel14, Ck.rel15, Ck.rel16, Ck.rel17,
    Ck.rel18, Ck.rel19, Ck.rel20, Ck.rel21, Ck.rel22, Ck.rel23, Ck.rel24, Ck.rel25]

theorem frame_facts : FrameN := by
  obtain ⟨p1, p2⟩ := and_t Ck.pts_t
  obtain ⟨f1, f2⟩ := and_t Ck.frm_t
  obtain ⟨f3, f4⟩ := and_t f2
  obtain ⟨f5, f6⟩ := and_t f4
  obtain ⟨f7, f8⟩ := and_t f6
  obtain ⟨f9, f10⟩ := and_t f8
  refine ⟨by rw [← ptC_eq]; exact beq_t p1, by rw [← ptC_eq]; exact beq_t p2, beq_t f1, beq_t f3,
    ⟨beq_t f5, beq_t f7, beq_t f9, beq_t f10⟩, ?_, ?_, by decide +kernel, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
    have h := cj_all i (by rw [base_len] at hi; exact hi)
    unfold cj at h
    rw [nthD_eq 0 base i hi] at h
    have e := beq_t h
    rw [ptC_eq, ptC_eq] at e
    rw [e]
    unfold xQ
    rw [xP_eq]
  · intro j hj p hp
    have h := allL_spec Ck.ef_t (nthD [] eps j) (nthD_mem [] (by have : eps.length = 6 := rfl; omega))
    have := beq_t (allL_spec h p hp)
    rw [ptC_eq] at this
    exact this
  · intro i hi b hb
    have h := rel_all i hi
    unfold rel at h
    have := beq_t (allL_spec h b hb)
    rw [ptC_eq] at this
    exact this
  · have := nbeq_t Ck.e0m_t
    rw [ptC_eq] at this
    exact this

structure ScanN : Prop where
  cover : ∀ a < 306936, ∃ v, InW hw v ∧ cP NW NT v a ∈ gh
  rep : ∀ y ∈ gh, ¬ PpN OL NT c0 c1 y ∨ (PP.testBit y = true ∧
    ((PpN OL NT c0 c1 y ∧ ∃ q < 306936, PpN OL NT c0 c1 q ∧ q ≠ y ∧ clsK OL NT y q = q ∧
      clsK OL NT (xQ y) q ≠ q) ∨ y ∈ lam))
  pp_pts : ∀ x, PP.testBit x = true → x < 306936
  pcl : ∀ x < 306936, ∀ w ∈ hw, PP.testBit (cP NW NT w x) = true → PP.testBit x = true
  lam_cl : ∀ w ∈ hw, ∀ a ∈ lam, cP NW NT w a ∈ lam
  lamf : ∀ a ∈ lam, PpN OL NT c0 c1 a ∧ ∃ Wa Wx : List Nat, (∀ c ∈ Wa, c < 26) ∧
    (∀ c ∈ Wx, c < 26) ∧ cP NW NT Wa 0 = a ∧ cP NW NT Wx 0 = xQ a ∧
    ∀ q < 306936, PP.testBit q = true → q ≠ a → TF Wa q → TF Wx q

theorem gh_len : gh.length = 12 := by decide

theorem lam_len : lam.length = 6 := rfl

theorem wq_lt : ∀ i < 12, nthD 0 wq i < 306936 := by decide +kernel

theorem lw_lt : ∀ j < 6, (∀ c ∈ (nthD ([], []) lw j).1, c < 26) ∧ ∀ c ∈ (nthD ([], []) lw j).2, c < 26 := by
  decide +kernel

theorem stk_all : ∀ i < 12, stk i = true := by
  intro i hi
  interval_cases i
  exacts [Ck.stk0, Ck.stk1, Ck.stk2, Ck.stk3, Ck.stk4, Ck.stk5, Ck.stk6, Ck.stk7, Ck.stk8, Ck.stk9,
    Ck.stk10, Ck.stk11]

theorem lmk_all : ∀ j < 6, lmk j = true := by
  intro j hj
  interval_cases j
  exacts [Ck.lmk0, Ck.lmk1, Ck.lmk2, Ck.lmk3, Ck.lmk4, Ck.lmk5]

theorem or_t {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd h (by decide)

theorem memB_spec {y : Nat} : ∀ {l : List Nat}, memB y l = true → y ∈ l
  | [], h => by
    change false = true at h
    exact absurd h (by decide)
  | a :: l, h => by
    rcases or_t h with h | h
    · rw [beq_t h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (memB_spec h)

theorem hw_lt : ∀ w ∈ hw, ∀ c ∈ w, c < 26 := by decide +kernel

theorem scan_facts : ScanN := by
  obtain ⟨g1, g2⟩ := and_t Ck.ghk_t
  have hg := allI_spec g2
  obtain ⟨q1, q2⟩ := and_t Ck.ppc_t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a ha
    have hx := cP_pts (fun c hc => by have := invC_lt G1_lt c hc; omega) ha
    obtain ⟨v, hv, hr'⟩ := free_facts.hcov _ hx
    refine ⟨v, hv, ?_⟩
    rw [cP_conj, cP_invC' G1_lt] at hr'
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hr'
    have hi' : i < gh.length := by
      have : hr.length = 12 := free_facts.hr_len
      rw [gh_len]
      omega
    have h := hg i hi'
    rw [Nat.zero_add, nthD_eq 0 hr i hi, e] at h
    have e2 := beq_t h
    rw [ptC_eq, cP_invC' G1_lt] at e2
    rw [e2]
    exact List.getElem_mem hi'
  ·
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
    have h := stk_all i (by rw [gh_len] at hi; exact hi)
    unfold stk at h
    rw [nthD_eq 0 gh i hi] at h
    beta_reduce at h
    by_cases hp : PpN OL NT c0 c1 gh[i]
    · rw [ppB_spec.2 hp] at h
      rcases or_t h with h | h
      · exact absurd h (by decide)
      · obtain ⟨h1, h2⟩ := and_t h
        refine Or.inr ⟨bit_of h1, ?_⟩
        rcases or_t h2 with h | h
        · obtain ⟨a1, a2, a3, a4⟩ := failB_spec h
          exact Or.inl ⟨hp, _, wq_lt i (by rw [gh_len] at hi; exact hi), a1, a2, a3, a4⟩
        · exact Or.inr (memB_spec h)
    · exact Or.inl hp
  ·
    intro x hx
    have e : (PP &&& ptsM).testBit x = PP.testBit x := by rw [← nland, beq_t q1]
    rw [Nat.testBit_and, hx, Bool.true_and] at e
    by_contra hc
    rw [ptsM_bit' hc] at e
    exact absurd e (by decide)
  ·
    intro x hx w hw hP
    exact closW_spec vn q2 (by omega) hw hP
  ·
    intro w hw a ha
    have h := memB_spec (allL_spec (allL_spec Ck.lmp_t w hw) a ha)
    rwa [ptC_eq] at h
  ·
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
    have hj' : j < 6 := by rw [lam_len] at hj; exact hj
    have h := lmk_all j hj'
    unfold lmk at h
    rw [nthD_eq 0 lam j hj] at h
    beta_reduce at h
    obtain ⟨l1, l2, l3, l4⟩ := lamOK_spec vn h
    exact ⟨l1, _, _, (lw_lt j hj').1, (lw_lt j hj').2, l2, l3, fun q hq hP hqa hA => l4 q hq hP hqa hA⟩

end CFSG.KD.Fi24FreeK

end
