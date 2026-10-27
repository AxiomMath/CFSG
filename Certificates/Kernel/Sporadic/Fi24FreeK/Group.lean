module

public import Certificates.Kernel.Sporadic.Fi24FreeK.Facts
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24FreeFacts
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KD.Fi24FreeK.Group

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.HardMathSupport.Dickson.I271.TabFi24
open CFSG.Sporadic.Fi24 (R J JR jR tR cls root gs)
open CFSG.Perm CFSG.KC CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO CFSG.KC.Fi24FreeK CFSG.KS.Fi24ThreeO
  CFSG.KS.Fi24FreeK CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO CFSG.KD.Fi24ThreeO.Group
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW evalW_nil evalW_cons
  lift_mk_eq_evalW)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem frWc0_eq : CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native.frWc0 = CFSG.KD.Fi24FreeK.wc0 :=
  rfl

theorem frWc1_eq : CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native.frWc1 = CFSG.KD.Fi24FreeK.wc1 :=
  rfl

theorem frG1_eq : CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native.frG1 = G1 := rfl

theorem frEps_get (i : Fin 6) :
    CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native.frEps[i.val]! = nthD [] eps i.val := by
  fin_cases i <;> rfl

theorem wc0_lt : ∀ l ∈ CFSG.KD.Fi24FreeK.wc0, l < 26 := by decide

theorem wc1_lt : ∀ l ∈ CFSG.KD.Fi24FreeK.wc1, l < 26 := by decide

theorem val_A (hB : Bridge) : frA.val = CFSG.KD.Fi24FreeK.c0 := by
  unfold frA
  rw [frWc0_eq, root_val _ hB wc0_lt]
  exact frame_facts.c0w

theorem val_B (hB : Bridge) : frB.val = CFSG.KD.Fi24FreeK.c1 := by
  unfold frB
  rw [frWc1_eq, root_val _ hB wc1_lt]
  exact frame_facts.c1w

theorem xFr_val (hB : Bridge) (p : Fin 306936) :
    (xFr • p).val = xP OL NT CFSG.KD.Fi24FreeK.c0 CFSG.KD.Fi24FreeK.c1 p.val := by
  unfold xFr
  simp only [mul_smul]
  rw [hB.cls, hB.cls, hB.cls, hB.cls, val_A hB, val_B hB, xP_eq]
  rfl

theorem conjJ (hB : Bridge) : jR (wordElt G1 * wordElt [2]) = xFr * jR (wordElt G1) := by
  have hmem : xFr ∈ JR := by
    unfold xFr
    exact JR.mul_mem (cls_mul_cls_mem_JR fr0 fr1) (cls_mul_cls_mem_JR frA frB)
  obtain ⟨u, hu⟩ := exists_jR_of_mem hmem
  have e : wordElt G1 * wordElt [2] = u * wordElt G1 := by
    apply eq_of_base
    intro t ht
    apply Fin.ext
    rw [← wordElt_append, word_val hB _ (by decide +kernel), mul_smul,
      ← CFSG.Sporadic.Fi24.jR_smul u, hu, xFr_val hB, word_val hB _ G1_lt]
    rw [frame_facts.conj _ (base_mem t ht), xP_eq]
  rw [e, map_mul, hu]

theorem jR_xw (hB : Bridge) : jR (wordElt xw) = xFr := by
  have e : wordElt xw = wordElt G1 * wordElt [2] * (wordElt G1)⁻¹ := by
    unfold xw
    rw [wordElt_append, show 2 :: invC G1 = [2] ++ invC G1 from rfl, wordElt_append,
      wordElt_invC hB G1_lt, mul_assoc]
  rw [e, map_mul, conjJ hB, map_inv, mul_inv_cancel_right]

theorem fix_comm {g : J} {k : Fin 306936} (h : g • k = k) : jR g * cls k = cls k * jR g :=
  (smul_eq_iff_commute g k).1 h

theorem eps_fix4 (hB : Bridge) {j : ℕ} (hj : j < 6) :
    wordElt (nthD [] eps j) • fr0 = fr0 ∧ wordElt (nthD [] eps j) • fr1 = fr1 ∧
      wordElt (nthD [] eps j) • frA = frA ∧ wordElt (nthD [] eps j) • frB = frB := by
  have hf := frame_facts.efix j hj
  have hl := eps_lt j hj
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
  · rw [word_val hB _ hl]
    exact hf 0 List.mem_cons_self
  · rw [word_val hB _ hl]
    exact hf 305530 (List.mem_cons_of_mem _ List.mem_cons_self)
  · rw [word_val hB _ hl, val_A hB]
    exact hf _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [word_val hB _ hl, val_B hB]
    exact hf _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))

theorem eps_commX (hB : Bridge) {j : ℕ} (hj : j < 6) :
    jR (wordElt (nthD [] eps j)) * xFr = xFr * jR (wordElt (nthD [] eps j)) := by
  obtain ⟨f0, f1, fA, fB⟩ := eps_fix4 hB hj
  unfold xFr
  have c0 := fix_comm f0
  have c1 := fix_comm f1
  have cA := fix_comm fA
  have cB := fix_comm fB
  simp only [← mul_assoc, c0]
  rw [mul_assoc (cls fr0), c1, ← mul_assoc, mul_assoc _ (jR _), cA, ← mul_assoc,
    mul_assoc _ (jR _), cB, ← mul_assoc]

@[expose] def encL (x : Fin 6 × Bool) : ℕ := if x.2 then x.1.val else 6 + x.1.val

theorem rl_eq : CFSG.GH74.QTGen4.Recog.G23.g23Words.map (fun r => r.map encL) = rl := by
  decide +kernel

theorem epsW_true (i : Fin 6) : epsW i.val = nthD [] eps i.val := by
  unfold epsW
  rw [blt_of i.2]

theorem epsW_false (i : Fin 6) : epsW (6 + i.val) = invC (nthD [] eps i.val) := by
  unfold epsW
  have : Nat.blt (6 + i.val) 6 = false := by
    cases h : Nat.blt (6 + i.val) 6
    · rfl
    · exact absurd (blt_t h) (by omega)
  rw [this]
  change invC (nthD [] eps (6 + i.val - 6)) = _
  rw [Nat.add_sub_cancel_left]

theorem evalW_enc (hB : Bridge) :
    ∀ r : List (Fin 6 × Bool), evalW frE r = wordElt (epsL (r.map encL))
  | [] => rfl
  | x :: r => by
    rw [evalW_cons, evalW_enc hB r, List.map_cons]
    change _ = wordElt (epsW (encL x) ++ epsL (r.map encL))
    rw [wordElt_append]
    congr 1
    obtain ⟨i, b⟩ := x
    unfold frE
    rw [frEps_get]
    cases b
    · change (wordElt (nthD [] eps i.val))⁻¹ = wordElt (epsW (6 + i.val))
      rw [epsW_false, wordElt_invC hB (eps_lt i.val i.2)]
    · change wordElt (nthD [] eps i.val) = wordElt (epsW i.val)
      rw [epsW_true]

theorem epsL_lt : ∀ l : List ℕ, (∀ c ∈ l, c < 12) → ∀ x ∈ epsL l, x < 26
  | [], _, x, hx => absurd hx List.not_mem_nil
  | c :: l, h, x, hx => by
    change x ∈ epsW c ++ epsL l at hx
    rcases List.mem_append.1 hx with hx | hx
    · have hc := h c List.mem_cons_self
      by_cases h6 : c < 6
      · have e : epsW c = nthD [] eps c := by
          unfold epsW
          rw [blt_of h6]
        rw [e] at hx
        exact eps_lt c h6 x hx
      · have e : epsW c = invC (nthD [] eps (c - 6)) := by
          unfold epsW
          have : Nat.blt c 6 = false := by
            cases e' : Nat.blt c 6
            · rfl
            · exact absurd (blt_t e') h6
          rw [this]
          rfl
        rw [e] at hx
        exact invC_lt (eps_lt (c - 6) (by omega)) x hx
    · exact epsL_lt l (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) x hx

theorem rl_lt : ∀ i < 26, ∀ c ∈ nthD [] rl i, c < 12 := by decide +kernel

theorem freeFrameFacts_of (hB : Bridge) : FreeFrameFacts := by
  have hF := frame_facts
  have cv : ∀ k p : Fin 306936, (cls k • p).val = clsK OL NT k.val p.val := hB.cls
  have ncm : ∀ {k p : Fin 306936}, clsK OL NT k.val p.val ≠ p.val → cls k * cls p ≠ cls p * cls k :=
    fun h e => h (by rw [← cv]; exact congrArg Fin.val ((comm_iff _ _).1 e))
  have cm : ∀ {k p : Fin 306936}, clsK OL NT k.val p.val = p.val → cls k * cls p = cls p * cls k :=
    fun h => (comm_iff _ _).2 (Fin.ext (by rw [cv]; exact h))
  have m1 : (cls fr0 • fr1).val = 73618 := by rw [cv]; exact hF.m1
  have m2 : (cls frA • frB).val = 65697 := by rw [cv, val_A hB, val_B hB]; exact hF.m2
  have ne : ∀ {p q : Fin 306936}, p.val ≠ q.val → p ≠ q := fun h e => h (congrArg Fin.val e)
  have vA := val_A hB
  have vB := val_B hB
  refine ⟨ncm (by change clsK OL NT 0 305530 ≠ 305530; rw [hF.m1]; decide),
    ncm (by rw [vA, vB, hF.m2]; decide), cm (by rw [vA]; exact hF.cm.1),
    cm (by rw [vB]; exact hF.cm.2.1), cm (by rw [vA]; exact hF.cm.2.2.1),
    cm (by rw [vB]; exact hF.cm.2.2.2), ⟨ne ?_, ne ?_, ne ?_⟩, ⟨ne ?_, ne ?_, ne ?_⟩,
    ⟨ne ?_, ne ?_, ne ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals try (first
    | (rw [vA]; decide) | (rw [vB]; decide) | (rw [vA, m1]; decide) | (rw [vB, m1]; decide)
    | (rw [m2]; decide) | (rw [m2, m1]; decide))
  · rw [frG1_eq]
    exact conjJ hB
  · intro i
    unfold frE
    rw [frEps_get]
    exact eps_fix4 hB i.2
  · intro r hr
    rw [lift_mk_eq_evalW, evalW_enc hB]
    have hm : r.map encL ∈ rl := by
      rw [← rl_eq]
      exact List.mem_map_of_mem hr
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hm
    have hi' : i < 26 := by rw [hF.rl_len] at hi; exact hi
    rw [← e, ← nthD_eq [] rl i hi]
    have hl := epsL_lt _ (rl_lt i hi')
    apply eq_of_base
    intro t ht
    apply Fin.ext
    rw [word_val hB _ hl, one_smul]
    exact hF.rels i hi' _ (base_mem t ht)
  · refine ⟨0, fun h1 => hF.mv ?_⟩
    have := word_val hB _ (eps_lt 0 (by norm_num)) (⟨CFSG.KD.Fi24FreeK.mv, by decide +kernel⟩ :
      Fin 306936)
    unfold frE at h1
    rw [frEps_get] at h1
    rw [show ((0 : Fin 6) : ℕ) = 0 from rfl] at h1
    rw [h1, one_smul] at this
    exact this.symm

@[expose] def PpX (a : Fin 306936) : Prop :=
  cls a • (xFr • a) ≠ xFr • a ∧ xFr • xFr • a = cls a • (xFr • a)

@[expose] def QFailX (a : Fin 306936) : Prop :=
  ∃ q, PpX q ∧ q ≠ a ∧ cls a • q = q ∧ cls (xFr • a) • q ≠ q

theorem ppX_iff (hB : Bridge) (a : Fin 306936) :
    PpX a ↔ PpN OL NT CFSG.KD.Fi24FreeK.c0 CFSG.KD.Fi24FreeK.c1 a.val := by
  unfold PpX PpN
  rw [Ne, ← Fin.val_eq_val, ← Fin.val_eq_val, xFr_val hB, hB.cls, xFr_val hB, xFr_val hB,
    xFr_val hB]

theorem ppX_smul {r : R} (hr : r * xFr = xFr * r) (a : Fin 306936) : PpX (r • a) ↔ PpX a := by
  have hx : ∀ p : Fin 306936, xFr • r • p = r • xFr • p := fun p => by
    rw [← mul_smul, ← mul_smul, hr]
  have hc : ∀ p q : Fin 306936, cls (r • p) • (r • q) = r • (cls p • q) := fun p q => by
    rw [CFSG.Sporadic.Fi24.cls_smul_R, mul_smul, mul_smul, inv_smul_smul]
  unfold PpX
  have e2 : xFr • xFr • r • a = r • xFr • xFr • a := by rw [hx, hx]
  rw [e2, hx a, hc]
  simp only [ne_eq, smul_left_cancel_iff]

theorem qf_smul {r : R} (hr : r * xFr = xFr * r) {a : Fin 306936} (h : QFailX a) :
    QFailX (r • a) := by
  have hx : ∀ p : Fin 306936, xFr • r • p = r • xFr • p := fun p => by
    rw [← mul_smul, ← mul_smul, hr]
  have hc : ∀ p q : Fin 306936, cls (r • p) • (r • q) = r • (cls p • q) := fun p q => by
    rw [CFSG.Sporadic.Fi24.cls_smul_R, mul_smul, mul_smul, inv_smul_smul]
  obtain ⟨q, hq, hqa, h1, h2⟩ := h
  refine ⟨r • q, (ppX_smul hr q).2 hq, fun e => hqa (smul_left_cancel r e), ?_, ?_⟩
  · rw [hc, h1]
  · rw [hx, hc]
    exact fun e => h2 (smul_left_cancel r e)

theorem comm_inv_R {r : R} (hr : r * xFr = xFr * r) : r⁻¹ * xFr = xFr * r⁻¹ := by
  calc r⁻¹ * xFr = r⁻¹ * (xFr * r) * r⁻¹ := by group
    _ = r⁻¹ * (r * xFr) * r⁻¹ := by rw [hr]
    _ = xFr * r⁻¹ := by group

theorem qf_smul_iff {r : R} (hr : r * xFr = xFr * r) (a : Fin 306936) :
    QFailX (r • a) ↔ QFailX a := by
  refine ⟨fun h => ?_, qf_smul hr⟩
  have := qf_smul (comm_inv_R hr) h
  rwa [inv_smul_smul] at this

theorem hw_commX (hB : Bridge) {w : List ℕ} (hmem : w ∈ hw) :
    jR (wordElt w) * xFr = xFr * jR (wordElt w) := by
  unfold hw at hmem
  rcases List.mem_append.1 hmem with h | h
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
    have hl : eps.length = 6 := rfl
    rw [← nthD_eq [] eps j hj]
    exact eps_commX hB (by rw [hl] at hj; exact hj)
  · rw [List.mem_singleton.1 h, jR_xw hB]

theorem inw_commX (hB : Bridge) {v : List ℕ} (hv : InW hw v) :
    jR (wordElt v) * xFr = xFr * jR (wordElt v) := by
  obtain ⟨L, hL, rfl⟩ := hv
  induction L with
  | nil => rw [List.flatten_nil, wordElt_nil, map_one, one_mul, mul_one]
  | cons w L ih =>
    rw [List.flatten_cons, wordElt_append, map_mul, mul_assoc,
      ih (fun w' h' => hL w' (List.mem_cons_of_mem w h')), ← mul_assoc,
      hw_commX hB (hL w List.mem_cons_self), mul_assoc]

theorem inw_lt {v : List ℕ} (hv : InW hw v) : ∀ l ∈ v, l < 26 :=
  InW_lt CFSG.KD.Fi24FreeK.hw_lt hv

theorem pp_pull {v : List ℕ} (hv : InW hw v) {x : ℕ} (hx : x < 306936)
    (h : PP.testBit (cP NW NT v x) = true) : PP.testBit x = true := by
  obtain ⟨L, hL, rfl⟩ := hv
  induction L with
  | nil => exact h
  | cons w L ih =>
    rw [List.flatten_cons, cP_append] at h
    have hlt : cP NW NT L.flatten x < 306936 :=
      cP_pts (fun c hc => by
        have := inw_lt ⟨L, fun w' h' => hL w' (List.mem_cons_of_mem w h'), rfl⟩ c hc
        omega) hx
    exact ih (fun w' h' => hL w' (List.mem_cons_of_mem w h'))
      (scan_facts.pcl _ hlt w (hL w List.mem_cons_self) h)

theorem lam_push {v : List ℕ} (hv : InW hw v) {x : ℕ} (hx : x ∈ lam) : cP NW NT v x ∈ lam := by
  obtain ⟨L, hL, rfl⟩ := hv
  induction L with
  | nil => exact hx
  | cons w L ih =>
    rw [List.flatten_cons, cP_append]
    exact scan_facts.lam_cl w (hL w List.mem_cons_self) _
      (ih (fun w' h' => hL w' (List.mem_cons_of_mem w h')))

theorem to_rep (hB : Bridge) (a : Fin 306936) :
    ∃ v, InW hw v ∧ (wordElt v • a).val ∈ gh := by
  obtain ⟨v, hv, h⟩ := scan_facts.cover a.val a.2
  exact ⟨v, hv, by rw [word_val hB v (inw_lt hv)]; exact h⟩

theorem smul_eq_jR (g : J) (a : Fin 306936) : g • a = jR g • a :=
  (CFSG.Sporadic.Fi24.jR_smul g a).symm

theorem pp_of (hB : Bridge) {q : Fin 306936} (hq : PpX q) : PP.testBit q.val = true := by
  obtain ⟨v, hv, hy⟩ := to_rep hB q
  have hc := inw_commX hB hv
  have hP : PpX (wordElt v • q) := by rw [smul_eq_jR]; exact (ppX_smul hc q).2 hq
  rcases scan_facts.rep _ hy with h | ⟨h, -⟩
  · exact absurd ((ppX_iff hB _).1 hP) h
  · rw [word_val hB v (inw_lt hv)] at h
    exact pp_pull hv q.2 h

theorem lam_iff (hB : Bridge) (a : Fin 306936) : FrLam a ↔ a.val ∈ lam := by
  have vA := val_A hB
  have vB := val_B hB
  have m1 : (cls fr0 • fr1).val = 73618 := by rw [hB.cls]; exact frame_facts.m1
  have m2 : (cls frA • frB).val = 65697 := by rw [hB.cls, vA, vB]; exact frame_facts.m2
  unfold FrLam
  simp only [Fin.ext_iff, vA, vB, m1, m2]
  change _ ↔ a.val ∈ [0, 305530, 73618, 254589, 61582, 65697]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rfl

theorem lam_good (hB : Bridge) {a : Fin 306936} (ha : a.val ∈ lam) : PpX a ∧ ¬ QFailX a := by
  obtain ⟨hp, Wa, Wx, hWa, hWx, ea, ex, hT⟩ := scan_facts.lamf _ ha
  refine ⟨(ppX_iff hB a).2 hp, ?_⟩
  rintro ⟨q, hq, hqa, h1, h2⟩
  have eA : wordElt Wa • root = a := Fin.ext (by rw [root_val Wa hB hWa, ea])
  have eX : wordElt Wx • root = xFr • a := Fin.ext (by rw [root_val Wx hB hWx, ex, xFr_val hB]; rfl)
  have t1 : TF Wa q.val := (TF_iff hB hWa q).2 (by rw [eA]; exact h1)
  have t2 := hT q.val q.2 (pp_of hB hq) (fun e => hqa (Fin.ext e)) t1
  rw [TF_iff hB hWx q, eX] at t2
  exact h2 t2

theorem lam_of (hB : Bridge) {b : Fin 306936} (hp : PpX b) (hq : ¬ QFailX b) : b.val ∈ lam := by
  obtain ⟨v, hv, hy⟩ := to_rep hB b
  have hc := inw_commX hB hv
  have hP : PpX (wordElt v • b) := by rw [smul_eq_jR]; exact (ppX_smul hc b).2 hp
  have hQ : ¬ QFailX (wordElt v • b) := by rw [smul_eq_jR, qf_smul_iff hc]; exact hq
  have hy' : (wordElt v • b).val ∈ lam := by
    rcases scan_facts.rep _ hy with h | ⟨-, ⟨-, q, hqlt, h1, h2, h3, h4⟩ | h⟩
    · exact absurd ((ppX_iff hB _).1 hP) h
    · refine absurd ⟨⟨q, hqlt⟩, (ppX_iff hB _).2 h1, fun e => h2 (congrArg Fin.val e), ?_, ?_⟩ hQ
      · exact Fin.ext (by rw [hB.cls]; exact h3)
      · intro e
        apply h4
        have := congrArg Fin.val e
        rw [hB.cls, xFr_val hB] at this
        exact this
    · exact h
  classical
  let S : Finset (Fin 306936) := Finset.univ.filter fun p => p.val ∈ lam
  have hS : ∀ p ∈ S, wordElt v • p ∈ S := fun p hp' => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp' ⊢
    rw [word_val hB v (inw_lt hv)]
    exact lam_push hv hp'
  have hyS : wordElt v • b ∈ S := by simp [S, hy']
  obtain ⟨p, hpS, e⟩ := Finset.surj_on_of_inj_on_of_card_le (fun p _ => wordElt v • p) hS
    (fun p₁ p₂ _ _ h => smul_left_cancel _ h) le_rfl _ hyS
  have hb : b = p := smul_left_cancel _ e
  rw [hb]
  simpa [S] using hpS

theorem freeLamFacts_of (hB : Bridge) : FreeLamFacts := by
  intro g hg a ha
  rw [lam_iff hB] at ha ⊢
  obtain ⟨hp, hq⟩ := lam_good hB ha
  refine lam_of hB ?_ ?_
  · rw [smul_eq_jR]
    exact (ppX_smul hg a).2 hp
  · rw [smul_eq_jR, qf_smul_iff hg]
    exact hq

end CFSG.KD.Fi24FreeK.Group

end
