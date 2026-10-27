module

public import Certificates.Kernel.Fi22Syl.Chain
public import Certificates.Kernel.Fi22Syl.LeafChecks
public import Certificates.Kernel.Fi22Core.Conj
public import Certificates.Kernel.Fi22Core.OrbData
public import Certificates.Certificate1005
public import CFSG.Sporadic.Fi22.Simple
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22S.leafAll CertificateChecks.KernelFi22S.leafSl 128

namespace CertificateChecks.KernelFi22S

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.TW CFSG.KS.Fi22L
  CFSG.KS.Fi22S CFSG.KS.Fi22Cent CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CertificateChecks.KernelFi22C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem orb_eq : orb = orbL := by
  unfold orb
  exact orbitData_eq

theorem allFixL_spec (F : Nat → Nat) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(Nat.beq (F q) q, ih)) l = true →
      ∀ q ∈ l, F q = q
  | [], _ => by simp
  | a :: l, h => by
    change bAnd(Nat.beq (F a) a, List.rec (motive := fun _ => Bool) true
      (fun q _ ih => bAnd(Nat.beq (F q) q, ih)) l) = true at h
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact allFixL_spec F l h.2 q hq

theorem anyMvL_spec (F : Nat → Nat) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) false (fun q _ ih => bIf(Nat.beq (F q) q, ih, true)) l = true →
      ∃ q ∈ l, F q ≠ q
  | [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | a :: l, h => by
    change bIf(Nat.beq (F a) a, List.rec (motive := fun _ => Bool) false
      (fun q _ ih => bIf(Nat.beq (F q) q, ih, true)) l, true) = true at h
    rw [Raw.Orb.bIf_eq] at h
    by_cases e : F a = a
    · rw [ite_eq_left (by rw [Nat.beq_eq]; exact e)] at h
      obtain ⟨q, hq, hne⟩ := anyMvL_spec F l h
      exact ⟨q, List.mem_cons_of_mem a hq, hne⟩
    · exact ⟨a, List.mem_cons_self, e⟩

theorem allFix_spec {F : Nat → Nat} (h : allFix F = true) : ∀ q ∈ QL, F q = q :=
  allFixL_spec F QL h

theorem anyMv_spec {F : Nat → Nat} (h : anyMv F = true) : ∃ q ∈ QL, F q ≠ q :=
  anyMvL_spec F QL h

theorem QL_lt : ∀ q ∈ QL, q < 3510 := by decide

@[expose] def InJ (f : Nat → Nat) : Prop := ∃ g : J, ∀ x < 3510, f x = idx 3510 g x

theorem InJ.lt {f : Nat → Nat} (h : InJ f) {x : Nat} (hx : x < 3510) : f x < 3510 := by
  obtain ⟨g, hg⟩ := h
  rw [hg x hx]
  exact idx_lt g hx

theorem InJ.comp {f g : Nat → Nat} (hf : InJ f) (hg : InJ g) : InJ fun x => f (g x) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a * b, fun x hx => ?_⟩
  beta_reduce
  rw [hb x hx, ha _ (idx_lt b hx), idx_mul]

theorem InJ.congr {f g : Nat → Nat} (hf : InJ f) (h : ∀ x < 3510, g x = f x) : InJ g := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun x hx => by rw [h x hx, ha x hx]⟩

theorem InJ.id : InJ fun x => x := ⟨1, fun x _ => by rw [idx_one]⟩

theorem InJ.eq_id {f : Nat → Nat} (hf : InJ f) (hQ : allFix f = true) : ∀ x < 3510, f x = x := by
  obtain ⟨g, hg⟩ := hf
  have hfix := allFix_spec hQ
  have h1 : g = 1 := sep g fun t ht => by
    have hm : chainQ[t]! ∈ QL := by
      rw [← chain_hyp.chk.1, getElem!_pos chainQ t ht]
      exact Array.getElem_mem_toList ht
    rw [← hg _ (QL_lt _ hm)]
    exact hfix _ hm
  intro x hx
  rw [hg x hx, h1, idx_one]

theorem inJ_LJ {l : Nat} (hl : l < 32) : InJ (LJk ljPacked slpPacked l) := by
  have hT : TR 3510 (chainLetters orb)[l]! (LJk ljPacked slpPacked l) := by
    rw [orb_eq]
    exact CertificateChecks.KernelFi22.Letters.letters.2.1 l hl
  refine ⟨pairG gs l, fun x hx => ?_⟩
  rw [← (hT.2 x hx).1]
  exact rep_pairG_all l (by rw [orb_eq, CertificateChecks.KernelFi22.Letters.letters.1]; exact hl) x hx

theorem inJ_wJ : ∀ w : List Nat, (∀ z ∈ w, z < 32) → InJ (wJ w)
  | [], _ => InJ.id.congr fun _ _ => rfl
  | z :: w, h => by
    refine ((inJ_LJ (h z List.mem_cons_self)).comp
      (inJ_wJ w fun z' hz' => h z' (List.mem_cons_of_mem z hz'))).congr fun x _ => ?_
    change strictN (wJ w x) (LJk ljPacked slpPacked z) = _
    rw [Raw.Orb.strictN_eq]

theorem swL_lt : ∀ j < 11, ∀ z ∈ swL.getD j [], z < 32 := by decide

theorem inJ_even {j : Nat} (hj : j < 11) : InJ (LSK (2 * j)) := by
  refine (inJ_wJ _ (swL_lt j hj)).congr fun x hx => ?_
  have h0 := swAll j hj
  unfold swS swChk at h0
  have h := Raw.Orb.allN_iff.1 h0 x hx
  rw [Nat.beq_eq] at h
  exact h

theorem inJ_LSK {l : Nat} (hl : l < 22) : InJ (LSK l) := by
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · exact inJ_even (by omega)
  · obtain ⟨g, hg⟩ := inJ_even (j := j) (by omega)
    have hj : j < 22 / 2 := by omega
    refine ⟨g⁻¹, fun y hy => ?_⟩
    have e : LSK (2 * j) (idx 3510 g⁻¹ y) = y := by
      rw [hg _ (idx_lt _ hy), idx_idx_inv]
    calc LSK (2 * j + 1) y = LSK (2 * j + 1) (LSK (2 * j) (idx 3510 g⁻¹ y)) := by rw [e]
      _ = idx 3510 g⁻¹ y := (invK_spec inv_ok hj (idx_lt _ hy)).2.2

theorem inJ_gA : InJ gA := by
  refine ⟨a, fun x hx => ?_⟩
  have e : ap orb.alpha x = gA x := by
    rw [orb_eq]
    exact (alpha_get hx).1
  rw [← e]
  exact rep_alpha x hx

theorem wPF_succ (i f k x : Nat) : wPF i (f + 1) k x =
    if 0 < k ∧ r32 (PARS i) k < k then LSK (r32 (LABS i) k) (wPF i f (r32 (PARS i) k) x) else x := by
  change Bool.rec (motive := fun _ => Nat) x
    (strictN (wPF i f (r32 (PARS i) k) x) (LSK (r32 (LABS i) k)))
    (Bool.rec (motive := fun _ => Bool) false (Nat.blt (r32 (PARS i) k) k) (Nat.blt 0 k)) = _
  rw [Raw.Orb.bAnd_eq, Raw.Orb.strictN_eq]
  by_cases hc : 0 < k ∧ r32 (PARS i) k < k
  · rw [ite_eq_left hc, show (Nat.blt 0 k && Nat.blt (r32 (PARS i) k) k) = true by
      simp [Nat.blt_eq, hc]]
  · rw [ite_eq_right hc, show (Nat.blt 0 k && Nat.blt (r32 (PARS i) k) k) = false from
      Bool.eq_false_iff.2 fun h => hc (by simpa [Nat.blt_eq] using h)]

theorem walkF_single (i : Nat) : ∀ f k x, walkF LSK (PARS i) (LABS i) f k [x] = [wPF i f k x]
  | 0, _, _ => rfl
  | f + 1, k, x => by
    rw [walkF_succ, wPF_succ]
    split_ifs
    · rw [walkF_single i f, mapK_eq]
      rfl
    · rfl

theorem wP_eq {i k x : Nat} (hi : i < 2) (hk : k < CNTS i) (hx : x < 3510) :
    wP i k x = actN (twL 3510 LSN PARS LABS i k) x := by
  have h := walkF_eq chain_hyp hi k k hk le_rfl [x] (by simpa using hx)
  rw [walkF_single] at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  exact h

theorem inJ_wPF {i : Nat} (hi : i < 2) : ∀ f k, k < CNTS i → k ≤ f → InJ (wPF i f k)
  | 0, k, _, hkf => by
    have : k = 0 := by omega
    subst this
    exact InJ.id.congr fun _ _ => rfl
  | f + 1, k, hk, hkf => by
    by_cases hc : 0 < k ∧ r32 (PARS i) k < k
    · have hl := (mem_lvK.1 (lab_mem chain_hyp hi hk hc.1)).1
      refine ((inJ_LSK hl).comp (inJ_wPF hi f _ (lt_trans hc.2 hk) (by omega))).congr
        fun x _ => ?_
      rw [wPF_succ, ite_eq_left hc]
    · exact InJ.id.congr fun x _ => by rw [wPF_succ, ite_eq_right hc]

theorem inJ_gK {k j : Nat} (hk : k < 1024) (hj : j < 128) : InJ (gK k j) := by
  obtain ⟨c0, c1⟩ := cnts
  refine ((inJ_wPF (i := 0) (by norm_num) k k (by rw [c0]; exact hk) le_rfl).comp
    (inJ_wPF (i := 1) (by norm_num) j j (by rw [c1]; exact hj) le_rfl)).congr fun x _ => ?_
  unfold gK
  rw [Raw.Orb.strictN_eq]
  rfl

noncomputable abbrev tabK (i : Nat) : Array Table :=
  treeTabs 3510 (chainTrees 3510 LSN sylBase)[i]! LSN

theorem trees_get {i : Nat} (hi : i < 2) :
    (chainTrees 3510 LSN sylBase)[i]! = trK 3510 CNTS PTSS POSS PARS LABS i := by
  rw [chainTrees_eq chain_hyp, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem tabK_size {i : Nat} (hi : i < 2) : (tabK i).size = CNTS i := by
  unfold tabK treeTabs
  rw [Array.size_ofFn, trees_get hi, pts_size]

theorem tab_TR {i k : Nat} (hi : i < 2) (hk : k < CNTS i) : TR 3510 (tabK i)[k]! (wP i k) := by
  have hq : ∀ x ∈ Array.range 3510, x < 3510 := fun x hx => by simpa using hx
  have e1 : (tabK i)[k]! = (walk (trK 3510 CNTS PTSS POSS PARS LABS i) LSN k
      (Array.range 3510)).map UInt32.ofNat := by
    unfold tabK treeTabs
    rw [getElem!_pos _ k (by rw [Array.size_ofFn, trees_get hi, pts_size]; exact hk),
      Array.getElem_ofFn]
    change Array.map UInt32.ofNat (walk (chainTrees 3510 LSN sylBase)[i]! LSN k
      (Array.range 3510)) = _
    rw [trees_get hi]
  rw [e1, walk_eq chain_hyp hi k hk _ hq]
  refine ⟨by simp, fun x hx => ⟨?_, ?_⟩⟩
  · unfold ap
    rw [getElem!_pos _ x (by simpa using hx), Array.getElem_map, Array.getElem_map,
      Array.getElem_range, UInt32.toNat_ofNat', Nat.mod_eq_of_lt
        (lt_trans (actN_lt _ hx) (by norm_num)), wP_eq hi hk hx]
  · rw [wP_eq hi hk hx]
    exact actN_lt _ hx

theorem ap_compT' (P Q : Table) {x : Nat} (hx : x < 3510) :
    ap (compT 3510 P Q) x = ap P (ap Q x) := by
  unfold compT
  rw [CFSG.Sporadic.Th.ap_ofFn _ hx]
  rfl

theorem gA_lt' {x : Nat} (hx : x < 3510) : gA x < 3510 := (tree_facts hx).1

theorem gA_gA {x : Nat} (hx : x < 3510) : gA (gA x) = x := (tree_facts hx).2.2.1

theorem reg_zero (y : Nat) : reg ljPacked 0 y = gA y := by
  unfold reg Fi22Cent.gA
  rw [regT_lt (by norm_num)]

theorem reg_one (y : Nat) : reg ljPacked 1 y = gB y := by
  unfold reg Fi22Cent.gB
  rw [regT_lt (by norm_num)]

theorem gB_facts {x : Nat} (hx : x < 3510) :
    gB x < 3510 ∧ gBi x < 3510 ∧ gBi (gB x) = x ∧ gB (gBi x) = x := by
  obtain ⟨-, h1, h2, h3, h4⟩ := gen_facts CertificateChecks.KernelFi22.Letters.gen_ok hx
  rw [reg_one] at h1 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem wF_zero (x : Nat) : wF 0 x = gB x := rfl

theorem wI_zero (x : Nat) : wI 0 x = gBi x := rfl

theorem wF_one (x : Nat) : wF 1 x = gA (gB (gA (gB x))) := by
  change strictN (gB x) (fun y => strictN (gA y) fun z => strictN (gB z) gA) = _
  simp only [Raw.Orb.strictN_eq]

theorem wI_one (x : Nat) : wI 1 x = gBi (gA (gBi (gA x))) := by
  change strictN (gA x) (fun y => strictN (gBi y) fun z => strictN (gA z) gBi) = _
  simp only [Raw.Orb.strictN_eq]

theorem wF_facts {w : Nat} (hw : w < 2) {x : Nat} (hx : x < 3510) :
    wF w x < 3510 ∧ wI w x < 3510 ∧ wI w (wF w x) = x ∧ wF w (wI w x) = x := by
  interval_cases w
  · rw [wF_zero, wI_zero, wI_zero, wF_zero]
    exact gB_facts hx
  · rw [wF_one, wI_one, wI_one, wF_one]
    obtain ⟨b1, -, b3, -⟩ := gB_facts hx
    obtain ⟨b1', -, b3', -⟩ := gB_facts (gA_lt' b1)
    have a1 := gA_lt' hx
    obtain ⟨-, c2, -, c4⟩ := gB_facts a1
    obtain ⟨-, c2', -, c4'⟩ := gB_facts (gA_lt' c2)
    refine ⟨gA_lt' b1', c2', ?_, ?_⟩
    · rw [gA_gA b1', b3', gA_gA b1, b3]
    · rw [c4', gA_gA c2, c4, gA_gA hx]

theorem conjWords_get {w : Nat} (hw : w < 2) :
    ∀ x < 3510, ((conjWords ())[w]!).foldr (gz ljPacked) x = wF w x := by
  intro x _
  interval_cases w
  · change gz ljPacked 2 x = gB x
    simp [gz, reg_one]
  · change gz ljPacked 1 (gz ljPacked 2 (gz ljPacked 1 (gz ljPacked 2 x))) = wF 1 x
    simp [gz, reg_one, reg_zero, wF_one]

theorem conj_size : (conjTabs orbL).size = 2 := by
  unfold conjTabs
  rw [Array.size_map]
  rfl

theorem conj_TR {w : Nat} (hw : w < 2) :
    TR 3510 ((conjTabs orbL)[w]'(by rw [conj_size]; exact hw)).1 (wF w) ∧
      TR 3510 ((conjTabs orbL)[w]'(by rw [conj_size]; exact hw)).2 (wI w) := by
  have h1 : TR 3510 (wordT 3510 (genTables orbL) (conjWords ())[w]!) (wF w) :=
    TR_congr (wordT_TR (n := 3510) (by norm_num) (gens := genTables orbL) (G := gz ljPacked)
      (conjWords ())[w]! fun z _ => tr_gen CertificateChecks.KernelFi22.Letters.gen_ok z)
      (conjWords_get hw)
  have e : (conjTabs orbL)[w]'(by rw [conj_size]; exact hw) =
      (wordT 3510 (genTables orbL) (conjWords ())[w]!,
        invT 3510 (wordT 3510 (genTables orbL) (conjWords ())[w]!)) := by
    unfold conjTabs
    rw [Array.getElem_map, getElem!_pos (conjWords ()) w (by change w < 2; exact hw)]
  rw [e]
  refine ⟨h1, invT_TR (by norm_num) h1 fun x hx => ?_⟩
  obtain ⟨-, f2, f3, f4⟩ := wF_facts hw hx
  exact ⟨f2, f4, f3⟩

theorem leafK_of {k j : Nat} (hk : k < 1024) (hj : j < 128) : leafK k j = true := by
  have hs : k / 8 < 128 := by omega
  have h := leafAll (k / 8) hs
  unfold leafSl at h
  have h' := Raw.Orb.allN_iff.1 h (k % 8) (Nat.mod_lt _ (by norm_num))
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add (Nat.mul (k / 8) 8) (k % 8) = k := by
    exact Nat.div_add_mod' k 8
  rw [e] at h'
  exact Raw.Orb.allN_iff.1 h' j hj

theorem not_allIn {p : Nat → Bool} {q : Nat} (hq : q < 3510) (h : p q = false) :
    allIn 0 3510 p = false := by
  rw [Bool.eq_false_iff]
  intro hp
  rw [TW.allIn_iff.1 hp q hq] at h
  exact absurd h (by decide)

theorem order3OK_of {X : Table} {H : Nat → Nat} (hX : ∀ x < 3510, ap X x = H x ∧ H x < 3510)
    (h : ∀ x < 3510, H (H (H x)) = x) : order3OK 3510 X = true := by
  unfold order3OK
  rw [TW.allIn_iff]
  intro i hi
  obtain ⟨a1, a2⟩ := hX i hi
  obtain ⟨b1, b2⟩ := hX _ a2
  rw [a1, b1, (hX _ b2).1, h i hi, beq_self_eq_true]

theorem tests_of {R : Table} {G : Nat → Nat} {w : Nat}
    (hR : ∀ x < 3510, ap R x = rK G w x ∧ rK G w x < 3510)
    (h : conjK G w = true) : (!idOK 3510 R && !invoOK 3510 R && !order3OK 3510 R) = true := by
  unfold conjK at h
  rw [Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨m1, m2, m3⟩ := h
  obtain ⟨q1, hq1, n1⟩ := anyMv_spec m1
  obtain ⟨q2, hq2, n2⟩ := anyMv_spec m2
  obtain ⟨q3, hq3, n3⟩ := anyMv_spec m3
  have l1 := QL_lt q1 hq1
  have l2 := QL_lt q2 hq2
  have l3 := QL_lt q3 hq3
  unfold sq at n2
  unfold cb at n3
  simp only [Raw.Orb.strictN_eq] at n2 n3
  have e1 : idOK 3510 R = false := not_allIn l1 (by rw [(hR q1 l1).1]; simpa using n1)
  have e2 : invoOK 3510 R = false := not_allIn l2 (by
    rw [(hR q2 l2).1, (hR _ (hR q2 l2).2).1]; simpa using n2)
  have e3 : order3OK 3510 R = false := not_allIn l3 (by
    rw [(hR q3 l3).1, (hR _ (hR q3 l3).2).1, (hR _ (hR _ (hR q3 l3).2).2).1]; simpa using n3)
  rw [e1, e2, e3]
  rfl

theorem conj_leaf {P : Table} {G : Nat → Nat} (hG : InJ G) (hP : ∀ x < 3510, ap P x = G x)
    {w : Nat} (hw : w < 2) (hc : conjK G w = true) :
    (!idOK 3510 (compT 3510 P (compT 3510 (compT 3510
        ((conjTabs orbL)[w]'(by rw [conj_size]; exact hw)).1 P)
        ((conjTabs orbL)[w]'(by rw [conj_size]; exact hw)).2)) &&
      !invoOK 3510 (compT 3510 P (compT 3510 (compT 3510
        ((conjTabs orbL)[w]'(by rw [conj_size]; exact hw)).1 P)
        ((conjTabs orbL)[w]'(by rw [conj_size]; exact hw)).2)) &&
      !order3OK 3510 (compT 3510 P (compT 3510 (compT 3510
        ((conjTabs orbL)[w]'(by rw [conj_size]; exact hw)).1 P)
        ((conjTabs orbL)[w]'(by rw [conj_size]; exact hw)).2))) = true := by
  obtain ⟨T1, T2⟩ := conj_TR hw
  refine tests_of (fun x hx => ?_) hc
  obtain ⟨a1, a2⟩ := T2.2 x hx
  have b := hG.lt a2
  obtain ⟨c1, c2⟩ := T1.2 _ b
  rw [ap_compT' _ _ hx, ap_compT' _ _ hx, a1, ap_compT' _ _ a2, hP _ a2, c1, hP _ c2]
  unfold rK
  simp only [Raw.Orb.strictN_eq, true_and]
  exact hG.lt c2

theorem leaf_ok {k j : Nat} (hk : k < 1024) (hj : j < 128) :
    leafOK orbL.alpha (conjTabs orbL) (compT 3510 (tabK 0)[k]! (tabK 1)[j]!) = true := by
  obtain ⟨c0, c1⟩ := cnts
  set P := compT 3510 (tabK 0)[k]! (tabK 1)[j]! with hPdef
  have hG := inJ_gK hk hj
  have hP : ∀ x < 3510, ap P x = gK k j x := by
    intro x hx
    have t1 := (tab_TR (i := 1) (by norm_num) (by rw [c1]; exact hj)).2 x hx
    rw [hPdef, ap_compT' _ _ hx, t1.1, ((tab_TR (i := 0) (by norm_num)
      (by rw [c0]; exact hk)).2 _ t1.2).1]
    unfold gK
    rw [Raw.Orb.strictN_eq]
  have hl := leafK_of hk hj
  unfold leafK leafF at hl
  simp only [Raw.Orb.bIf_eq] at hl
  unfold leafOK
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  split_ifs at hl with h1 h2 h3 h4
  ·
    obtain ⟨q, hq, hne⟩ := anyMv_spec h1
    have hq' := QL_lt q hq
    refine Or.inl (Or.inl (Or.inl (not_allIn hq' ?_)))
    rw [hP q hq', hP _ (hG.lt hq')]
    unfold sq at hne
    rw [Raw.Orb.strictN_eq] at hne
    simpa using hne
  ·
    refine Or.inl (Or.inl (Or.inr ?_))
    unfold idOK
    rw [TW.allIn_iff]
    intro i hi
    rw [hP i hi, hG.eq_id h2 i hi, beq_self_eq_true]
  ·
    have hH : InJ fun x => strictN (gA x) (gK k j) :=
      (hG.comp inJ_gA).congr fun x _ => Raw.Orb.strictN_eq _ _
    have hC : InJ (cb fun x => strictN (gA x) (gK k j)) :=
      (hH.comp (hH.comp hH)).congr fun x _ => by unfold cb; simp only [Raw.Orb.strictN_eq]
    refine Or.inl (Or.inr (order3OK_of (H := fun x => gK k j (gA x)) (fun x hx => ⟨?_, ?_⟩)
      fun x hx => ?_))
    · rw [ap_compT' _ _ hx, (alpha_get hx).1]
      change ap P (Fi22Cent.gA x) = _
      rw [hP _ (gA_lt' hx)]
    · exact hG.lt (gA_lt' hx)
    · have e := hC.eq_id h3 x hx
      unfold cb at e
      simp only [Raw.Orb.strictN_eq] at e
      exact e
  · right
    rw [Array.any_eq_true]
    exact ⟨0, by rw [conj_size]; norm_num, conj_leaf hG hP (by norm_num) h4⟩
  · right
    rw [Array.any_eq_true]
    exact ⟨1, by rw [conj_size]; norm_num, conj_leaf hG hP (by norm_num) hl⟩

theorem syl_ok : sylChecks orbL 3 = true := by
  obtain ⟨c0, c1⟩ := cnts
  unfold sylChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, chain_eq.2 3⟩, sizes⟩, ?_⟩, ?_⟩
  · rw [CertificateChecks.KernelFi22.Letters.letters.1, Array.all_eq_true]
    intro w hw
    have hw' : w < 11 := hw
    rw [List.all_eq_true]
    intro z hz
    rw [decide_eq_true_eq]
    exact (sw_eq w hw').2 z (by rw [getElem!_pos _ w hw]; exact hz)
  · rw [Array.all_eq_true]
    intro w hw
    rw [conj_size] at hw
    obtain ⟨T1, T2⟩ := conj_TR hw
    exact invOK_of T1 T2 fun i hi => (wF_facts hw hi).2.2.1
  · apply parAll_of
    intro k hk
    change k < (tabK 0).size at hk
    rw [tabK_size (by norm_num), c0] at hk
    rw [Array.all_eq_true]
    intro j hj
    change j < (tabK 1).size at hj
    have hj' := hj
    rw [tabK_size (by norm_num), c1] at hj'
    rw [← getElem!_pos (tabK 1) j hj]
    exact leaf_ok hk hj'

end CertificateChecks.KernelFi22S

end
