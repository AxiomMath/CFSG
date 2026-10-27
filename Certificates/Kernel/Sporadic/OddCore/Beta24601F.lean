module

public import Certificates.Kernel.Sporadic.OddCore.Beta24601K
public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5F
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.RuInvHash

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B24601

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CertificateChecks.KernelSpor.J3BetaA5 (natArr_get hkey_inj_of idxTH_of memTH_of)

local notation "⟪" x "⟫" => tabT (unpack 315 9 x)

theorem treeImg_eq (pg : Array Table) (par lab : Array ℕ) (m : ℕ) :
    treeImg pg par lab m = (List.range' 1 (m - 1)).foldl
      (fun r j => r.push (compT 6 r[par[j]!]! pg[lab[j]!]!)) #[idT 6] := by
  unfold treeImg
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one,
    Nat.add_sub_cancel, List.forIn_pure_yield_eq_foldl, bind_pure]
  rfl

theorem permOK_of_pK {x : Table} (h : pK x = true) :
    CFSG.Sporadic.SmallOddCore.permOK 6 x = true := by
  unfold CFSG.Sporadic.SmallOddCore.permOK CFSG.Monster.B.Co2.Native.isInvA
  rw [CFSG.KC.Misc.RuInv.P.invCand_eq_foldl, allLt_iff']
  intro i hi
  unfold pK invL6 at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.2 hi)
  simpa only [natArr_get] using this

theorem tblEq6_eq (x y : Table) : tblEq 6 x y = eq6 x y := by
  unfold tblEq eq6
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, List.all_eq_true]
  simp only [List.mem_range]

theorem base : szOK 315 9 = true ∧ S16J2.cK J2Cn.idK = true ∧
    CFSG.KS.Prim.idK 315 9 (mask 9) = true ∧ S16J2.cK (J2BetaT.F 7) = true ∧
    S16J2.cK (B24601I 2) = true ∧ S16J2.iK (J2BetaT.F 7) (B24601I 2) = true ∧
    allN 2 (fun j => bAnd(S16J2.cK (B24601R.GI j), bAnd(S16J2.cK (B24601I j),
      bAnd(S16J2.iK (B24601R.GI j) (B24601I j),
      bAnd(Nat.beq (B24601R.GI j) (J2BetaT.F (Nat.add j 8)), bAnd(Nat.beq (B24601R.G j) J2Cn.idK,
      J2Cn.commK (J2BetaT.F 7) (B24601R.GI j))))))) = true ∧
    J2Cn.isId 3 (J2BetaT.F 7) = true ∧ J2Cn.notId 1 (J2BetaT.F 7) = true ∧
    J2Cn.sK (J2BetaT.F 8) = true ∧ J2Cn.sK (J2BetaT.F 9) = true ∧ J2Cn.sK (J2BetaT.F 7) = true ∧
    Nat.beq (J2BetaT.F 8) (J2Cn.F 31) = true ∧ Nat.beq B24601R.cnt 1080 = true ∧
    penumHdK J2Cn.idK B24601R.cnt 1100 B24601R.T B24601R.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hcnt : B24601R.cnt = 1080 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hidc : canonK 315 9 (mask 9) (315 * 9) (pidn 315 9) = true := base.2.1

theorem hid : idT 315 = ⟪pidn 315 9⟫ := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem hbc : canonK 315 9 (mask 9) (315 * 9) (J2BetaT.F 7) = true := base.2.2.2.1

theorem gen {j : ℕ} (hj : j < 2) : S16J2.cK (B24601R.GI j) = true ∧ S16J2.cK (B24601I j) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) (B24601R.GI j) (B24601I j) = true ∧
    B24601R.GI j = J2BetaT.F (j + 8) ∧ B24601R.G j = pidn 315 9 ∧
    J2Cn.commK (J2BetaT.F 7) (B24601R.GI j) = true := by
  have h := allN_spec base.2.2.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem beta_tab {k : ℕ} (hk : k < 13) : j2BetaTbl k = ⟪J2BetaT.F k⟫ := by
  have h : natArr (j2BetaTbl k) = unpack 315 9 (J2BetaT.F k) := by
    have h := CFSG.KC.Misc.HexFlat.hexT_sound J2BetaT.all (by norm_num) k hk
    rw [← J2BetaT.eq] at h
    exact h
  rw [← tabT_natArr (j2BetaTbl k), h]

@[expose] noncomputable def gensK : Array Table := #[⟪B24601R.GI 0⟫, ⟪B24601R.GI 1⟫]

theorem gens_eq : #[j2BetaTbl 8, j2BetaTbl 9] = gensK := by
  rw [beta_tab (by norm_num), beta_tab (by norm_num), ← (gen (j := 0) (by norm_num)).2.2.2.1,
    ← (gen (j := 1) (by norm_num)).2.2.2.1]
  rfl

theorem s_tabs : TabsOK 315 9 2 B24601R.GI gensK := by
  refine ⟨rfl, fun j hj => ⟨?_, (gen hj).1⟩⟩
  interval_cases j <;> (rw [getElem!_pos _ _ (by simp [gensK])]; simp [gensK])

theorem s_pe : ∀ i < B24601R.cnt, penumPtK 315 9 (mask 9) (315 * 9) true B24601R.G B24601R.GI 2
    B24601R.cnt B24601R.T B24601R.PL B24601R.POS B24601R.SRT B24601R.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < B24601R.cnt,
    hsortPtK 315 9 (mask 9) B24601R.cnt B24601R.T B24601R.HS B24601R.HSI i = true :=
  fun i hi => slK_spec sH i (Nat.zero_le _) (by omega) hi

theorem s_cl : ∀ c < B24601R.cnt * 4, findPtK B24601R.cnt B24601R.T
    (prodQK 315 9 (mask 9) 4 B24601R.T (bothK 2 B24601R.GI B24601I)) B24601Cl c = true :=
  fun c hc => slK_spec sCl c (Nat.zero_le _) (by change c < Nat.mul B24601R.cnt 4; omega)
    (by change c < Nat.mul B24601R.cnt 4; omega)

theorem mul_eq : mulClosureH 315 gensK 1100 = hRec 315 9 B24601R.cnt B24601R.T B24601R.PL ∧
    mulTreeOK 315 gensK (hRec 315 9 B24601R.cnt B24601R.T B24601R.PL).1
      (hRec 315 9 B24601R.cnt B24601R.T B24601R.PL).2.1
      (hRec 315 9 B24601R.cnt B24601R.T B24601R.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 B24601R.cnt B24601R.T B24601R.PL).1.toList = true :=
  mulH_sound base.1 (fun j hj => (gen hj).2.2.2.2.1) s_tabs base.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    s_pe s_hs

theorem hT {i : ℕ} (hi : i < 1080) : canonK 315 9 (mask 9) (315 * 9) (B24601R.T i) = true :=
  penumPt_canon (s_pe i (by rw [hcnt]; exact hi))

@[expose] noncomputable def LK : Array Table := (hRec 315 9 1080 B24601R.T B24601R.PL).1

theorem LK_size : LK.size = 1080 := hRec_size _ _ _ _ _

theorem LK_get {i : ℕ} (hi : i < 1080) : LK[i]! = ⟪B24601R.T i⟫ := hRec_get hi

theorem mul_eq' : mulClosureH 315 gensK 1100 = hRec 315 9 1080 B24601R.T B24601R.PL := by
  rw [← hcnt]
  exact mul_eq.1

theorem LK_inj : ∀ a < LK.size, ∀ b < LK.size, hkey 315 LK[a]! = hkey 315 LK[b]! → a = b := by
  have h := mul_eq.2.2
  rw [hcnt] at h
  exact hkey_inj_of h

theorem prod_entry {k l : ℕ} (hk : k < 1080) (hl : l < 4) :
    r32 B24601Cl (k * 4 + l) < 1080 ∧
      compT 315 LK[k]! (gensK ++ gensK.map (invT 315))[l]! = LK[r32 B24601Cl (k * 4 + l)]! := by
  have hb := TabsOK_both s_tabs (fun j hj => ⟨(gen hj).2.2.1, (gen hj).2.1⟩)
  obtain ⟨hgj, hcj⟩ := hb.2 l hl
  have hc : k * 4 + l < B24601R.cnt * 4 := by rw [hcnt]; omega
  obtain ⟨hq, he⟩ := findPt_spec (s_cl _ hc)
  unfold prodQK at he
  obtain ⟨e1, e2⟩ := div_mod_pair (i := k) hl
  change r32 B24601Cl (k * 4 + l) < B24601R.cnt at hq
  rw [show Nat.div (k * 4 + l) 4 = k from e1, show Nat.mod (k * 4 + l) 4 = l from e2] at he
  rw [hcnt] at hq
  refine ⟨hq, ?_⟩
  rw [LK_get hk, hgj, compT_unpack (hT hk) hcj, ← he, LK_get hq]

theorem fold_ofFn {pg : Array Table} {par lab : Array ℕ} {L : ℕ → Table} {m : ℕ}
    (h0 : L 0 = idT 6)
    (hs : ∀ k, 1 ≤ k → k < m → par[k]! < k ∧ L k = compT 6 (L par[k]!) pg[lab[k]!]!) :
    ∀ j, j < m → (List.range' 1 j).foldl (fun r k => r.push (compT 6 r[par[k]!]! pg[lab[k]!]!))
      #[idT 6] = Array.ofFn (n := j + 1) fun i => L i.val := by
  intro j
  induction j with
  | zero =>
    intro _
    apply Array.ext (by simp)
    intro i h1 _
    have hi : i = 0 := by simpa using h1
    subst hi
    simp [h0]
  | succ j ih =>
    intro hj
    rw [List.range'_concat, List.foldl_append, ih (by omega), Nat.one_mul]
    simp only [List.foldl_cons, List.foldl_nil]
    obtain ⟨hp, hL⟩ := hs (1 + j) (by omega) (by omega)
    rw [Array.ofFn_succ (n := j + 1)]
    have hg : (Array.ofFn (n := j + 1) fun i => L i.val)[par[1 + j]!]! = L par[1 + j]! := by
      rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
    rw [hg, ← hL, Nat.add_comm 1 j]
    rfl

@[expose] noncomputable def IK : Array Table := Array.ofFn (n := 1080) fun i => labT i.val

theorem cay : (∀ k < 1080, cayAt k = true) ∧ labT 0 = idT 6 ∧ piGens.toList.all pK = true := by
  have hc := cay_ok
  unfold cayK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  exact ⟨hc.1.1, hc.1.2, List.all_eq_true.2 hc.2⟩

theorem cayAt_spec {k : ℕ} (hk : k < 1080) : pK (labT k) = true ∧
    (k = 0 ∨ (parOf B24601R.PL k < k ∧
      labT k = compT 6 (labT (parOf B24601R.PL k)) piGens[labOf B24601R.PL k]!)) ∧
    (∀ l < 2, r32 B24601Cl (4 * k + l) < 1080 ∧
      eq6 (labT (r32 B24601Cl (4 * k + l))) (compT 6 (labT k) piGens[l]!) = true) ∧
    eq6 (labT k) (idT 6) = kerK (B24601R.T k) := by
  have h := cay.1 k hk
  unfold cayAt at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, fun l hl => h3 l hl, h4⟩

theorem par_get {k : ℕ} (hk : k < 1080) :
    (hRec 315 9 1080 B24601R.T B24601R.PL).2.1[k]! = parOf B24601R.PL k := by
  unfold hRec
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]

theorem lab_get {k : ℕ} (hk : k < 1080) :
    (hRec 315 9 1080 B24601R.T B24601R.PL).2.2[k]! = labOf B24601R.PL k := by
  unfold hRec
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]

theorem himg : treeImg piGens (hRec 315 9 1080 B24601R.T B24601R.PL).2.1
    (hRec 315 9 1080 B24601R.T B24601R.PL).2.2 LK.size = IK := by
  rw [treeImg_eq, LK_size]
  have hs : ∀ k, 1 ≤ k → k < 1080 →
      (hRec 315 9 1080 B24601R.T B24601R.PL).2.1[k]! < k ∧
        labT k = compT 6 (labT (hRec 315 9 1080 B24601R.T B24601R.PL).2.1[k]!)
          piGens[(hRec 315 9 1080 B24601R.T B24601R.PL).2.2[k]!]! := by
    intro k hk1 hk
    rw [par_get hk, lab_get hk]
    rcases (cayAt_spec hk).2.1 with h | h
    · omega
    · exact h
  exact fold_ofFn (L := labT) (m := 1080) cay.2.1 hs 1079 (by norm_num)

theorem IK_get {k : ℕ} (hk : k < 1080) : IK[k]! = labT k := by
  unfold IK
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]

theorem eq6_self (x : Table) : eq6 x x = true := by
  unfold eq6
  simp

theorem ker_eq {k : ℕ} (hk : k < 1080) :
    (tblEq 315 LK[k]! (idT 315) || tblEq 315 LK[k]! (j2BetaTbl 7) ||
      tblEq 315 LK[k]! (compT 315 (j2BetaTbl 7) (j2BetaTbl 7))) = kerK (B24601R.T k) := by
  rw [LK_get hk, hid, beta_tab (by norm_num), compT_unpack hbc hbc, tblEq_unpack (hT hk) hidc,
    tblEq_unpack (hT hk) hbc, tblEq_unpack (hT hk) (canonK_pcomp hbc hbc)]
  rfl

theorem facts24601a : j2BetaOK = true := by
  obtain ⟨-, c0, c6⟩ := cay
  obtain ⟨-, -, -, -, -, hIb, -, ho3, ho1, -⟩ := base
  unfold j2BetaOK betaHomCheck
  dsimp only
  rw [gens_eq, mul_eq']
  rw [show (hRec 315 9 1080 B24601R.T B24601R.PL).1 = LK from rfl, himg]
  simp only [Bool.and_eq_true]
  have g0 := gen (j := 0) (by norm_num)
  have g1 := gen (j := 1) (by norm_num)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← Array.all_toList]
    simp only [gensK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact permOK_unpack g0.1 g0.2.2.1
    · rw [invT_unpack (by norm_num) g0.2.2.1]
      exact invOK_unpack g0.1 g0.2.1 g0.2.2.1
    · exact permOK_unpack g1.1 g1.2.2.1
    · rw [invT_unpack (by norm_num) g1.2.2.1]
      exact invOK_unpack g1.1 g1.2.1 g1.2.2.1
  · rw [beta_tab (by norm_num)]
    exact permOK_unpack hbc hIb
  · rw [← Array.all_toList, List.all_eq_true]
    exact fun x hx => permOK_of_pK (List.all_eq_true.1 c6 x hx)
  · rw [beta_tab (by norm_num), J2Cn.ordF hbc 3]
    change (J2Cn.isId 3 (J2BetaT.F 7) && (J2Cn.notId 1 (J2BetaT.F 7) && true)) = true
    rw [ho3, ho1]
    rfl
  · rw [← Array.all_toList, beta_tab (by norm_num)]
    simp only [gensK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by rw [J2Cn.commF hbc g0.1]; exact g0.2.2.2.2.2,
      by rw [J2Cn.commF hbc g1.1]; exact g1.2.2.2.2.2⟩
  · have h := mul_eq.2.1
    rw [hcnt] at h
    exact h
  · have h := mul_eq.2.2
    rw [hcnt] at h
    exact h
  · unfold closedOKH
    rw [Array.all_eq_true]
    intro i hi
    rw [Array.all_eq_true]
    intro l hl
    have hi' : i < 1080 := by rw [← LK_size]; exact hi
    have hl' : l < 4 := by simpa [s_tabs.1] using hl
    obtain ⟨hq, he⟩ := prod_entry hi' hl'
    rw [← getElem!_pos LK i hi, ← getElem!_pos _ l hl, he]
    exact memTH_of LK_inj (by rw [LK_size]; exact hq) (by rw [LK_get hq]; exact tblEq_self (hT hq))
  · rw [LK_size]
    rfl
  · rw [LK_size]
    simp [IK]
  · rw [Array.all_eq_true]
    intro k hk
    have hk' : k < 1080 := by simpa [IK] using hk
    rw [← getElem!_pos IK k hk, IK_get hk']
    exact permOK_of_pK (cayAt_spec hk').1
  · rw [tblEq6_eq, IK_get (by norm_num), c0]
    exact eq6_self _
  · rw [LK_size, List.all_eq_true]
    intro k hk
    rw [List.all_eq_true]
    intro l hl
    have hk' := List.mem_range.1 hk
    have hl' := List.mem_range.1 hl
    obtain ⟨hq, he⟩ := prod_entry hk' (l := l) (by omega)
    have hg : (gensK ++ gensK.map (invT 315))[l]! = gensK[l]! := by
      rw [getElem!_pos _ l (by simp [s_tabs.1]; omega), getElem!_pos _ l (by rw [s_tabs.1]; omega),
        Array.getElem_append_left]
    rw [hg] at he
    rw [he, idxTH_of LK_inj (by rw [LK_size]; exact hq) (by rw [LK_get hq]; exact tblEq_self (hT hq)),
      tblEq6_eq, Nat.mul_comm k 4]
    obtain ⟨d1, d2⟩ := (cayAt_spec hk').2.2.1 l hl'
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨d1, ?_⟩
    rw [IK_get d1, IK_get hk']
    exact d2
  · rw [LK_size, List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    rw [tblEq6_eq, ker_eq hk', IK_get hk', (cayAt_spec hk').2.2.2]
    exact beq_self_eq_true _

theorem facts24601b : j2MemOK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h8, h9, h7, h31, -⟩ := base
  have g0 := gen (j := 0) (by norm_num)
  have g1 := gen (j := 1) (by norm_num)
  have c8 : canonK 315 9 (mask 9) (315 * 9) (J2BetaT.F 8) = true := by rw [← g0.2.2.2.1]; exact g0.1
  have c9 : canonK 315 9 (mask 9) (315 * 9) (J2BetaT.F 9) = true := by rw [← g1.2.2.2.1]; exact g1.1
  unfold j2MemOK
  rw [beta_tab (k := 8) (by norm_num), beta_tab (k := 9) (by norm_num),
    beta_tab (k := 7) (by norm_num), J2Cn.tabF (k := 31) (by norm_num),
    J2Cn.sift_eq c8, J2Cn.sift_eq c9, J2Cn.sift_eq hbc, tblEq_unpack c8 (J2Cn.Fc (by norm_num))]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h8, h9⟩, h7⟩, h31⟩

end CertificateChecks.KernelSpor.B24601

end
