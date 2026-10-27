module

public import Certificates.Kernel.Sporadic.Fi24F4.WC
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group
public import Certificates.Kernel.Sporadic.Fi24Base.Glue
public import CFSG.Certificates.Kernel.Spor.Fi24F4WSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi24WitFacts

public section

namespace CFSG.KD.Fi24F4

open CFSG.KC CFSG.KC.Fi24F4W CFSG.KS.Fi24F4W CFSG.KC.Fi24Kit CFSG.KS.Fi24Kit CFSG.KS.Fi24Net
open CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO.Group CFSG.KS.Fi24ThreeO
open CFSG.KD.Fi24Orb (OL)
open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24)
open CFSG.EvenSporadicStandard.YS14
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three (wordElt)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction


theorem smul_eq_iff_comm (r : R) (k : Fin 306936) : r • k = k ↔ r * cls k = cls k * r := by
  constructor
  · intro h
    have e := CFSG.Sporadic.Fi24.cls_smul_R r k
    rw [h] at e
    calc r * cls k = r * cls k * r⁻¹ * r := by group
      _ = cls k * r := by rw [← e]
  · intro h
    apply CFSG.Sporadic.Fi24.cls_injective
    rw [CFSG.Sporadic.Fi24.cls_smul_R, h, mul_inv_cancel_right]

theorem cls_not_mem_JR' (k : Fin 306936) : cls k ∉ JR := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Sporadic.Fi24.cls_mem k)
  apply CFSG.Sporadic.Fi24.tR_not_mem_JR
  have h' := CFSG.Sporadic.Fi24.normal_JR.conj_mem _ h c⁻¹
  rwa [← hc, show c⁻¹ * (c * tR * c⁻¹) * c⁻¹⁻¹ = tR by group] at h'

theorem cls_mul_cls_mem_JR' (k l : Fin 306936) : cls k * cls l ∈ JR :=
  (Subgroup.mul_mem_iff_of_index_two CFSG.Sporadic.Fi24.index_JR).2
    (iff_of_false (cls_not_mem_JR' k) (cls_not_mem_JR' l))

theorem mul_self_D24 {x : R} (hx : x ∈ D24) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  calc c * tR * c⁻¹ * (c * tR * c⁻¹) = c * (tR * tR) * c⁻¹ := by group
    _ = 1 := by rw [CFSG.Sporadic.Fi24.tR_mul_tR, mul_one, mul_inv_cancel]

theorem rtg_symm' {α : Type*} {r : α → α → Prop} (hs : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hs _ _ hbc) ih

theorem cube_of_ne' {x y : R} (hx : x ∈ D24) (hy : y ∈ D24) (hne : x * y ≠ y * x) :
    (x * y) ^ 3 = 1 := by
  rcases CFSG.Sporadic.Fi24.orderOf_mul_mem_D24 hx hy with h | h | h
  · exfalso
    apply hne
    have h1 : x * y = 1 := orderOf_eq_one_iff.1 h
    have h2 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, mul_inv_cancel, inv_mul_cancel]
  · exfalso
    apply hne
    have h3 := pow_orderOf_eq_one (x * y)
    rw [h, sq] at h3
    have h4 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (mul_self_D24 hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left (mul_self_D24 hy)
    rw [h4, mul_inv_rev, hxi, hyi]
  · have := pow_orderOf_eq_one (x * y)
    rwa [h] at this

theorem sq_ne_one_of_comm {G : Type*} [Group G] {g p : G} (hg : g * g = 1) (hp : p * p = 1)
    (hne : g * p ≠ p * g) : g * p * (g * p) ≠ 1 := by
  intro h
  apply hne
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_left hg
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_left hp
  have := eq_inv_of_mul_eq_one_left h
  rw [mul_inv_rev, hgi, hpi] at this
  exact this

@[expose] def finP (q : ℕ) : Fin 306936 := ⟨q % 306936, Nat.mod_lt _ (by norm_num)⟩

theorem finP_val {q : ℕ} (hq : q < 306936) : (finP q).val = q := Nat.mod_eq_of_lt hq

theorem nthN_eq : ∀ (l : List ℕ) (i : ℕ), nthN l i = l.getD i 0
  | [], i => rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by
    change nthN l i = _
    rw [nthN_eq l i]
    rfl

theorem nthL_eq : ∀ (l : List (List ℕ)) (i : ℕ), nthL l i = l.getD i []
  | [], i => rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by
    change nthL l i = _
    rw [nthL_eq l i]
    rfl

theorem wN_eq_cP (cs : List ℕ) (hcs : ∀ l ∈ cs, l < 26) (x : ℕ) : wN NW cs x = cP NW NT cs x := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change LN NW c (wN NW cs x) = CF NW NT c (cP NW NT cs x)
    rw [ih fun l hl => hcs l (List.mem_cons_of_mem _ hl)]
    unfold CF
    rw [if_neg (by have := hcs c List.mem_cons_self; omega)]

theorem wv_of {cs : List ℕ} (hcs : ∀ l ∈ cs, l < 26) : WV NW cs := fun l hl =>
  CFSG.KD.Fi24Base.nv_LN (hcs l hl)

theorem nv_NT : CFSG.KS.Fi24Net.NV NT := (CFSG.KS.Fi24Net.net_spec CFSG.KD.Fi24Kit.Ck.n).1

theorem getD_mem' {α : Type*} {l : List α} {i : ℕ} (d : α) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem cls_val' (hB : Bridge) (k p : ℕ) (hk : k < 306936) (hp : p < 306936) :
    (cls (⟨k, hk⟩ : Fin 306936) • (⟨p, hp⟩ : Fin 306936)).val = clsK OL NT k p :=
  cls_val hB k p hk hp

theorem act_val (hB : Bridge) {a : ℕ} (ha : a < 306936) (y : Fin 306936) :
    (cls (finP a) • y).val = clsK OL NT a y.val := by
  rw [show finP a = ⟨a, ha⟩ from Fin.ext (finP_val ha)]
  exact cls_val' hB a y.val ha y.isLt

theorem wit_mem {i : ℕ} (h : wit i = true) :
    ∀ e ∈ W.E.getD i [], witOK OL NT (nthN W.q0 i) (nthN e 0) (nthN e 1) (nthN e 2) = true := by
  unfold wit at h
  generalize W.E.getD i [] = l at h ⊢
  induction l with
  | nil => intro e he; exact absurd he List.not_mem_nil
  | cons x l ih =>
    intro e he
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact ih h2 e he

theorem witFacts_of (hB : Bridge) {i : ℕ} {r : R}
    (hr : ∀ x : Fin 306936, (r • x).val = rG NW NT (nthL W.cs i) (tB i) x.val)
    (hrr : r * r = 1)
    (hcs : ∀ l ∈ nthL W.cs i, l < 26) (hpl : ∀ c ∈ W.prods.getD i [], ∀ l ∈ c, l < 26)
    (hQlt : ∀ q ∈ nthL W.Q i, q < 306936) (hQc : ∀ q ∈ nthL W.Qc i, q < 306936)
    (hElt : ∀ e ∈ W.E.getD i [], nthN e 0 < 306936 ∧ nthN e 1 < 306936 ∧ nthN e 2 < 306936)
    (hEQ : ∀ e ∈ W.E.getD i [], nthN e 1 ∈ nthL W.Q i)
    (hQcQ : ∀ q ∈ nthL W.Qc i, q ∈ nthL W.Q i)
    (hq0 : nthN (nthL W.Q i) 0 = nthN W.q0 i) (hQpos : 0 < (nthL W.Q i).length)
    (hx : nthN W.xd i < 306936 ∧ nthN W.x1 i < 306936)
    (hcov : cov i = true) (hprd : prd i = true) (hwit : wit i = true) (hgph : gph i = true)
    (hfixq : fixq i = true) (hnd : nd i = true) :
    WitFacts r := by
  set Q := nthL W.Q i with hQ
  set q₀ := nthN W.q0 i with hq₀
  set m := Q.length with hm
  have hq0lt : q₀ < 306936 := by
    rw [← hq0]
    exact hQlt _ (by rw [nthN_eq]; exact getD_mem' 0 hQpos)
  have hQget : ∀ j < m, nthN Q j ∈ Q := fun j hj => by
    rw [nthN_eq]
    exact getD_mem' 0 hj
  have hQidx : ∀ q ∈ Q, ∃ j < m, nthN Q j = q := fun q hq => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hq
    exact ⟨j, hj, by rw [nthN_eq, List.getD_eq_getElem _ _ hj, e]⟩
  set QF : List (Fin 306936) := Q.map finP with hQF
  have hmemQF : ∀ x : Fin 306936, x ∈ QF ↔ x.val ∈ Q := fun x => by
    rw [hQF, List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [finP_val (hQlt q hq)]
      exact hq
    · intro hx
      exact ⟨x.val, hx, Fin.ext (finP_val x.isLt)⟩
  have hrpt : ∀ x (hx : x < 306936), rPt NW NT (nthL W.cs i) (tB i) x =
      (r • (⟨x, hx⟩ : Fin 306936)).val :=
    fun x hx => by rw [rPt_eq, hr]
  unfold nd at hnd
  obtain ⟨hnd1, hnd2⟩ := andB_iff.1 hnd
  have hr1 : r ≠ 1 := by
    intro h1
    rw [hrpt _ hx.2, h1, one_smul, Nat.beq_refl] at hnd2
    exact Bool.noConfusion hnd2
  have hrq0 : r ≠ cls (finP q₀) := by
    intro h1
    rw [hrpt _ hx.1] at hnd1
    have e2 : (r • (⟨nthN W.xd i, hx.1⟩ : Fin 306936)).val = clsK OL NT q₀ (nthN W.xd i) := by
      rw [h1, act_val hB hq0lt]
    rw [e2, Nat.beq_refl] at hnd1
    exact Bool.noConfusion hnd1
  have hfix := qfixOK_spec hfixq
  have hrQ : ∀ q ∈ QF, r * cls q = cls q * r := fun q hq => by
    rw [← smul_eq_iff_comm]
    apply Fin.ext
    rw [hr]
    exact hfix _ ((hmemQF q).1 hq)
  have hcomm : ∀ a b : ℕ, a < 306936 → b < 306936 →
      (cls (finP a) * cls (finP b) = cls (finP b) * cls (finP a) ↔ clsK OL NT a b = b) := by
    intro a b ha hb
    rw [← smul_eq_iff_comm (cls (finP a)) (finP b), ← Fin.val_eq_val, act_val hB ha,
      finP_val hb]
  obtain ⟨hpar, hth⟩ := graphOK_spec hgph
  have hperf : evenSub (clsSet QF) ≤ ⁅evenSub (clsSet QF), evenSub (clsSet QF)⁆ := by
    have hS : ∀ x ∈ clsSet QF, ∃ j < m, x = cls (finP (nthN Q j)) := by
      rintro x ⟨q, hq, rfl⟩
      obtain ⟨j, hj, e⟩ := hQidx q.val ((hmemQF q).1 hq)
      exact ⟨j, hj, by rw [e, show finP q.val = q from Fin.ext (finP_val q.isLt)]⟩
    have hSm : ∀ j < m, cls (finP (nthN Q j)) ∈ clsSet QF := fun j hj =>
      ⟨finP (nthN Q j), (hmemQF _).2 (by rw [finP_val (hQlt _ (hQget j hj))]; exact hQget j hj), rfl⟩
    refine evenSub_perfect (clsSet QF) ?_ ?_ ?_ ?_
    · rintro p ⟨q, -, rfl⟩
      exact CFSG.Sporadic.Fi24.cls_mul_cls q
    · rintro p ⟨a, -, rfl⟩ q ⟨b, -, rfl⟩ hne
      exact cube_of_ne' (CFSG.Sporadic.Fi24.cls_mem a) (CFSG.Sporadic.Fi24.cls_mem b) hne
    · intro p hp q hq hne
      obtain ⟨a, ha, rfl⟩ := hS p hp
      obtain ⟨b, hb, rfl⟩ := hS q hq
      rcases hth a ha b hb with h | ⟨k, hk, h1, h2⟩
      · exact absurd ((hcomm _ _ (hQlt _ (hQget a ha)) (hQlt _ (hQget b hb))).2 h) hne
      · refine ⟨cls (finP (nthN Q k)), hSm k hk, ?_, ?_⟩
        · exact (hcomm _ _ (hQlt _ (hQget k hk)) (hQlt _ (hQget a ha))).2 h1
        · exact (hcomm _ _ (hQlt _ (hQget k hk)) (hQlt _ (hQget b hb))).2 h2
    ·
      have hreach : ∀ j < m, Relation.ReflTransGen
          (fun a b => a ∈ clsSet QF ∧ b ∈ clsSet QF ∧ a * b ≠ b * a)
          (cls (finP (nthN Q 0))) (cls (finP (nthN Q j))) := by
        intro j
        induction j using Nat.strong_induction_on with
        | _ j ih =>
          intro hj
          rcases hpar j hj with rfl | ⟨hlt, hne⟩
          · exact Relation.ReflTransGen.refl
          · refine Relation.ReflTransGen.tail (ih _ hlt (by omega)) ⟨hSm _ (by omega), hSm j hj, ?_⟩
            intro h
            exact hne ((hcomm _ _ (hQlt _ (hQget _ (by omega))) (hQlt _ (hQget j hj))).1 h)
      have hsymm : ∀ {a b : R}, Relation.ReflTransGen
          (fun a b => a ∈ clsSet QF ∧ b ∈ clsSet QF ∧ a * b ≠ b * a) a b →
          Relation.ReflTransGen (fun a b => a ∈ clsSet QF ∧ b ∈ clsSet QF ∧ a * b ≠ b * a) b a :=
        fun h => rtg_symm' (fun a b h => ⟨h.2.1, h.1, Ne.symm h.2.2⟩) h
      intro p hp q hq
      obtain ⟨a, ha, rfl⟩ := hS p hp
      obtain ⟨b, hb, rfl⟩ := hS q hq
      exact (hsymm (hreach a ha)).trans (hreach b hb)
  unfold prd at hprd
  obtain ⟨hlen, hprd'⟩ := andB_iff.1 hprd
  have hprod : ∀ j < (nthL W.Qc i).length, (∀ x : Fin 306936,
      ((cls (finP (nthN (nthL W.Qc i) j)) * cls (finP q₀)) • x).val =
        wN NW (nthL (W.prods.getD i []) j) x.val) ∧
      cls (finP (nthN (nthL W.Qc i) j)) * cls (finP q₀) =
        cls (finP q₀) * cls (finP (nthN (nthL W.Qc i) j)) := by
    intro j hj
    obtain ⟨h1, h2⟩ := andB_iff.1 (CFSG.KS.allN_spec hprd' j hj)
    have hqm : nthN (nthL W.Qc i) j ∈ nthL W.Qc i := by
      rw [nthN_eq]
      exact getD_mem' 0 hj
    have hcm : nthL (W.prods.getD i []) j ∈ W.prods.getD i [] := by
      rw [nthL_eq]
      exact getD_mem' [] (by rw [Nat.eq_of_beq_eq_true hlen]; exact hj)
    set q := nthN (nthL W.Qc i) j
    set c := nthL (W.prods.getD i []) j
    have hqlt : q < 306936 := hQc _ hqm
    have hcl : ∀ l ∈ c, l < 26 := hpl c hcm
    have hmemJ : cls (finP q) * cls (finP q₀) ∈ (jR).range := by
      rw [CFSG.Sporadic.Fi24.range_jR]
      exact cls_mul_cls_mem_JR' _ _
    obtain ⟨g, hg⟩ := hmemJ
    have hbase := prodOK_spec h1
    have hgw : g = wordElt c := eq_of_base fun t ht => by
      apply Fin.ext
      have hb : CFSG.Sporadic.Fi24.Native.chainBase[t]! ∈ baseL := by
        rw [chainBase_eq]
        interval_cases t <;> decide
      rw [word_val hB c hcl, ← wN_eq_cP c hcl, hbase _ hb, ← CFSG.Sporadic.Fi24.jR_smul, hg,
        mul_smul, act_val hB hqlt, act_val hB hq0lt]
    refine ⟨fun x => ?_, ?_⟩
    · rw [← hg, CFSG.Sporadic.Fi24.jR_smul, hgw, word_val hB c hcl, wN_eq_cP c hcl]
    · exact (hcomm _ _ hqlt hq0lt).2 (Nat.eq_of_beq_eq_true h2)
  refine ⟨hrr, hr1, QF, finP q₀, (hmemQF _).2 (by rw [finP_val hq0lt, ← hq0]; exact hQget 0 hQpos),
    hrQ, hrq0, hperf, ?_⟩
  intro p hpD hrp hpq
  obtain ⟨k, rfl⟩ := CFSG.Sporadic.Fi24.exists_cls hpD
  have hrk : r • k = k := (smul_eq_iff_comm r k).2 hrp
  have hkq : k.val ≠ q₀ := fun h => hpq (by
    congr 1
    exact Fin.ext (by rw [finP_val hq0lt, h]))
  have hkfix : rG NW NT (nthL W.cs i) (tB i) k.val = k.val := by
    rw [← hr, hrk]
  have hkF : k = finP k.val := Fin.ext (finP_val k.isLt).symm
  by_cases hE : ∃ e ∈ W.E.getD i [], nthN e 0 = k.val
  · obtain ⟨e, he, hek⟩ := hE
    obtain ⟨hl0, hl1, hl2⟩ := hElt e he
    have hw := witOK_spec (wit_mem hwit e he)
    refine ⟨finP (nthN e 1), (hmemQF _).2 (by rw [finP_val hl1]; exact hEQ e he), fun h1 => ?_⟩
    apply hw
    have e1 : ∀ y : Fin 306936, ((cls (finP (nthN e 1)) * cls (finP q₀) * cls k) • y).val =
        clsK OL NT (nthN e 1) (clsK OL NT q₀ (clsK OL NT (nthN e 0) y.val)) := fun y => by
      rw [mul_smul, mul_smul, act_val hB hl1, act_val hB hq0lt, hkF, act_val hB k.isLt, ← hek]
    have e2 := congrArg Fin.val (show ((cls (finP (nthN e 1)) * cls (finP q₀) * cls k) *
        (cls (finP (nthN e 1)) * cls (finP q₀) * cls k)) • (⟨nthN e 2, hl2⟩ : Fin 306936) =
        ⟨nthN e 2, hl2⟩ by rw [h1, one_smul])
    rw [mul_smul, e1, e1] at e2
    exact e2
  ·
    have hnot : ∃ c ∈ W.prods.getD i [], wN NW c k.val ≠ k.val := by
      by_contra hall
      push Not at hall
      unfold cov at hcov
      have hmem := coverOK_spec (wv_of hcs) (fun c hc => wv_of (hpl c hc)) nv_NT hcov k.isLt
        hkfix hall
      rcases List.mem_cons.1 hmem with h | h
      · exact hkq h
      · obtain ⟨e, he, hek⟩ := List.mem_map.1 h
        exact hE ⟨e, he, hek⟩
    obtain ⟨c, hc, hne⟩ := hnot
    obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hc
    have hj' : j < (nthL W.Qc i).length := by
      rw [← Nat.eq_of_beq_eq_true hlen]
      exact hj
    obtain ⟨hact, hcm⟩ := hprod j hj'
    have hcj : nthL (W.prods.getD i []) j = c := by
      rw [nthL_eq, List.getD_eq_getElem _ _ hj, hjc]
    have hqm : nthN (nthL W.Qc i) j ∈ nthL W.Qc i := by
      rw [nthN_eq]
      exact getD_mem' 0 hj'
    set q := nthN (nthL W.Qc i) j
    have hqlt : q < 306936 := hQc _ hqm
    have hgg : cls (finP q) * cls (finP q₀) * (cls (finP q) * cls (finP q₀)) = 1 := by
      calc cls (finP q) * cls (finP q₀) * (cls (finP q) * cls (finP q₀))
          = cls (finP q) * (cls (finP q₀) * cls (finP q)) * cls (finP q₀) := by group
        _ = cls (finP q) * (cls (finP q) * cls (finP q₀)) * cls (finP q₀) := by rw [← hcm]
        _ = (cls (finP q) * cls (finP q)) * (cls (finP q₀) * cls (finP q₀)) := by group
        _ = 1 := by rw [CFSG.Sporadic.Fi24.cls_mul_cls, CFSG.Sporadic.Fi24.cls_mul_cls, one_mul]
    have hgk : cls (finP q) * cls (finP q₀) * cls k ≠ cls k * (cls (finP q) * cls (finP q₀)) := by
      intro h
      have h' := (smul_eq_iff_comm _ k).2 h
      apply hne
      rw [← hcj, ← hact k, h']
    have hqQ : finP q ∈ QF := (hmemQF _).2 (by rw [finP_val hqlt]; exact hQcQ _ hqm)
    have hfin := sq_ne_one_of_comm (G := R) (g := cls (finP q) * cls (finP q₀)) (p := cls k) hgg
      (CFSG.Sporadic.Fi24.cls_mul_cls k) hgk
    exact ⟨finP q, hqQ, hfin⟩

end CFSG.KD.Fi24F4

end
