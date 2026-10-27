module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenGroups
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenFacts
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenPSL
public import Certificates.Kernel.Misc.ON.Base

public noncomputable section

namespace CertificateChecks.KernelMisc.ON.L37

attribute [local irreducible] dotProduct

open CFSG.KC.Misc.F7 CFSG.KC.Loop Subgroup
open CFSG.RankThree.Native.ONTriple hiding relOKM
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
open CertificateChecks.KernelMisc.ON (regOKK)

theorem nthN_map_range {n q : ℕ} (f : ℕ → ℕ) (hq : q < n) :
    nthN ((List.range n).map f) q = f q := by
  simp [nthN_eq, List.getD_eq_getElem?_getD, hq]

theorem buildL_eq (n : ℕ) (f : ℕ → ℕ) (k : List ℕ → Bool) :
    buildL n f k = k ((List.range n).map f) := by
  have h : ∀ (n : ℕ) (acc : List ℕ), Nat.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc)
      (fun i ih acc => strictB (f i) fun v => ih (List.cons v acc)) n acc =
      k ((List.range n).map f ++ acc) := by
    intro n
    induction n with
    | zero => intro acc; rfl
    | succ n ih =>
      intro acc
      refine (strictB_eq (f n) _).trans ?_
      refine (ih _).trans ?_
      simp [List.range_succ]
  have := h n []
  rw [List.append_nil] at this
  exact this

theorem snocN_eq (F : List ℕ) (v : ℕ) : snocN F v = F ++ [v] := by
  induction F with
  | nil => rfl
  | cons x F ih => exact congrArg (List.cons x) ih

theorem notB_eq (b : Bool) : notB b = !b := by cases b <;> rfl

theorem invW_aux (w acc : List (ℕ × Bool)) :
    List.rec (motive := fun _ => List (ℕ × Bool) → List (ℕ × Bool)) (fun acc => acc)
      (fun l _ ih acc => ih (List.cons (l.1, notB l.2) acc)) w acc =
      (w.map fun l => (l.1, !l.2)).reverse ++ acc := by
  induction w generalizing acc with
  | nil => rfl
  | cons l w ih =>
    refine (ih _).trans ?_
    simp [notB_eq]

theorem invW_eq (w : List (ℕ × Bool)) : invW w = (w.map fun l => (l.1, !l.2)).reverse := by
  have := invW_aux w []
  rw [List.append_nil] at this
  exact this

theorem mem_invW {w : List (ℕ × Bool)} {l : ℕ × Bool} (h : l ∈ invW w) : ∃ l' ∈ w, l'.1 = l.1 := by
  rw [invW_eq, List.mem_reverse, List.mem_map] at h
  obtain ⟨l', hl', rfl⟩ := h
  exact ⟨l', hl', rfl⟩

@[expose] def runL : List (List (ℕ × Bool)) → List ℕ → List ℕ → List ℕ × List ℕ
  | [], F, FI => (F, FI)
  | w :: p, F, FI => runL p (F ++ [wordC (nthN F) (nthN FI) w])
      (FI ++ [wordC (nthN F) (nthN FI) (invW w)])

theorem runK_spec : ∀ (prog : List (List (ℕ × Bool))) (F FI : List ℕ)
    (k : List ℕ → List ℕ → Bool), runK prog F FI k = k (runL prog F FI).1 (runL prog F FI).2
  | [], _, _, _ => rfl
  | w :: p, F, FI, k => by
    change strictB _ (fun v => strictB _ fun vi => runK p (snocN F v) (snocN FI vi) k) = _
    simp only [strictB_eq, snocN_eq]
    rw [runK_spec p]
    rfl

section Model

set_option linter.unusedSectionVars false

@[expose] def GRep (c : ℕ) (g : GM) : Prop := MRep c g.1

theorem grep_mmul {a b : ℕ} {g h : GM} (ha : GRep a g) (hb : GRep b h) :
    GRep (mmul a b) (g * h) := mrep_mmul ha hb

theorem grep_idM : GRep idM 1 := mrep_idM

theorem grep_powM {a : ℕ} {g : GM} (ha : GRep a g) (e : ℕ) : GRep (powM a e) (g ^ e) := by
  unfold GRep at *
  rw [SubgroupClass.coe_pow]
  exact mrep_powM ha e

theorem grep_eq {a b : ℕ} {g h : GM} (ha : GRep a g) (hb : GRep b h) (hab : Nat.beq a b = true) :
    g = h :=
  Subtype.ext (mrep_eq ha hb hab)

theorem grep_inv_of_sq {a : ℕ} {g : GM} (ha : GRep a g) (h : g * g = 1) : GRep a g⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right h]
  exact ha

theorem grep_wordF {F FI : ℕ → ℕ} (g : ℕ → GM) (w : List (ℕ × Bool))
    (h : ∀ l ∈ w, GRep (F l.1) (g l.1) ∧ GRep (FI l.1) (g l.1)⁻¹) :
    GRep (wordC F FI w) ((w.map fun l => if l.2 then g l.1 else (g l.1)⁻¹).prod) := by
  induction w with
  | nil => exact grep_idM
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have hl := h (i, b) List.mem_cons_self
    have hw := ih fun l hl => h l (List.mem_cons_of_mem _ hl)
    rw [List.map_cons, List.prod_cons]
    cases b with
    | true => exact grep_mmul hl.1 hw
    | false => exact grep_mmul hl.2 hw

theorem grep_wordC {F FI : ℕ → ℕ} {R : Array GM} (w : List (ℕ × Bool))
    (h : ∀ l ∈ w, GRep (F l.1) (R.getD l.1 1) ∧ GRep (FI l.1) (R.getD l.1 1)⁻¹) :
    GRep (wordC F FI w) (wordG R w) :=
  grep_wordF (fun r => R.getD r 1) w h

theorem wordG_invW (R : Array GM) (w : List (ℕ × Bool)) : wordG R (invW w) = (wordG R w)⁻¹ := by
  rw [invW_eq]
  unfold wordG
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left fun l _ => ?_
  obtain ⟨a, b⟩ := l
  cases b <;> simp

theorem grep_wordC_inv {F FI : ℕ → ℕ} {R : Array GM} (w : List (ℕ × Bool))
    (h : ∀ l ∈ w, GRep (F l.1) (R.getD l.1 1) ∧ GRep (FI l.1) (R.getD l.1 1)⁻¹) :
    GRep (wordC F FI (invW w)) (wordG R w)⁻¹ := by
  rw [← wordG_invW]
  refine grep_wordC _ fun l hl => ?_
  obtain ⟨l', hl', e⟩ := mem_invW hl
  rw [← e]
  exact h l' hl'

@[expose] def CRep (F FI : List ℕ) (R : Array GM) : Prop :=
  F.length = R.size ∧ FI.length = R.size ∧
    ∀ r < R.size, GRep (nthN F r) (R.getD r 1) ∧ GRep (nthN FI r) (R.getD r 1)⁻¹

theorem nthN_snoc_lt {F : List ℕ} {r : ℕ} (h : r < F.length) (v : ℕ) :
    nthN (F ++ [v]) r = nthN F r := by
  simp [nthN_eq, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem nthN_snoc_len (F : List ℕ) (v : ℕ) : nthN (F ++ [v]) F.length = v := by
  simp [nthN_eq, List.getD_eq_getElem?_getD]

theorem runL_rep : ∀ (prog : List (List (ℕ × Bool))) (F FI : List ℕ) (R : Array GM),
    CRep F FI R → progOK R.size prog = true →
      CRep (runL prog F FI).1 (runL prog F FI).2 (runG R (prog.map SOp.word))
  | [], _, _, _, h, _ => h
  | w :: p, F, FI, R, h, hp => by
    simp only [progOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hw, hp⟩ := hp
    have hl : ∀ l ∈ w, GRep (nthN F l.1) (R.getD l.1 1) ∧ GRep (nthN FI l.1) (R.getD l.1 1)⁻¹ :=
      fun l hl => h.2.2 _ (hw l hl)
    have hv := grep_wordC (F := nthN F) (FI := nthN FI) w hl
    have hvi := grep_wordC_inv (F := nthN F) (FI := nthN FI) w hl
    have hR : CRep (F ++ [wordC (nthN F) (nthN FI) w]) (FI ++ [wordC (nthN F) (nthN FI) (invW w)])
        (R.push (wordG R w)) := by
      refine ⟨by simp [h.1], by simp [h.2.1], fun r hr => ?_⟩
      rw [Array.size_push] at hr
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
      · rw [nthN_snoc_lt (h.1 ▸ hr), nthN_snoc_lt (h.2.1 ▸ hr), getD_push_lt _ _ hr]
        exact h.2.2 r hr
      · have e1 : nthN (F ++ [wordC (nthN F) (nthN FI) w]) R.size = wordC (nthN F) (nthN FI) w := by
          rw [← h.1]
          exact nthN_snoc_len F _
        have e2 : nthN (FI ++ [wordC (nthN F) (nthN FI) (invW w)]) R.size =
            wordC (nthN F) (nthN FI) (invW w) := by
          rw [← h.2.1]
          exact nthN_snoc_len FI _
        rw [e1, e2, getD_push_size]
        exact ⟨hv, hvi⟩
    have := runL_rep p _ _ _ hR (by rw [Array.size_push]; exact hp)
    exact this

theorem slp_spec {prog : List (List (ℕ × Bool))} {F0 : List ℕ} {R : Array GM} (h0 : CRep F0 F0 R)
    (hp : progOK R.size prog = true) {K : Subgroup GM} (hK : ∀ k, R.getD k 1 ∈ K) {t c : ℕ}
    {g : GM} (ht : t < R.size + prog.length) (hc : GRep c g)
    (hb : Nat.beq (nthN (runL prog F0 F0).1 t) c = true) : g ∈ K := by
  have hr := runL_rep prog F0 F0 R h0 hp
  have e := grep_eq (hr.2.2 t (by rw [size_runG, List.length_map]; exact ht)).1 hc hb
  rw [← e]
  exact runG_mem _ R hK t

theorem grep_xC {j l m i : ℕ} (hj : j < 2) (hl : l < 4) (hm : m < 3) (hi : i < 3) :
    GRep (xC j l m i) (xE j l m i) := by
  have hL := regOKK (rRegL j l) (rL_lt j hj l hl)
  have hV := (regOKK (rRegV j m i) (vRegI_lt j hj m hm i hi)).1
  have e : eM (rRegL j l) = (nL j l).1 := eM_rL hj hl
  rw [e] at hL
  exact mrep_mmul (mrep_mmul hL.2 hV) hL.1

theorem xE_sq {j l m i : ℕ} (hj : j < 2) (hm : m < 3) (hi : i < 3) :
    xE j l m i * xE j l m i = 1 := by
  have h := vG_sq hj hm hi
  unfold xE
  calc (nL j l)⁻¹ * vG j m i * nL j l * ((nL j l)⁻¹ * vG j m i * nL j l)
      = (nL j l)⁻¹ * (vG j m i * vG j m i) * nL j l := by group
    _ = 1 := by rw [h]; group

theorem xE_mul01 {j l m : ℕ} (hj : j < 2) (hm : m < 3) :
    xE j l m 0 * xE j l m 1 = xE j l m 2 := by
  have h := (chkV_facts hj hm).1
  unfold xE
  rw [← h]
  group

theorem xE_mul10 {j l m : ℕ} (hj : j < 2) (hm : m < 3) :
    xE j l m 1 * xE j l m 0 = xE j l m 2 := by
  have h := (chkV_facts hj hm).2.1
  unfold xE
  rw [← h]
  group

abbrev xQ (j q : ℕ) : GM := xE j (q / 9) (q / 3 % 3) (q % 3)

theorem xQ_eq {j a i : ℕ} (hi : i < 3) : xQ j (3 * a + i) = xE j (a / 3) (a % 3) i := by
  have h1 : (3 * a + i) / 9 = a / 3 := by omega
  have h2 : (3 * a + i) / 3 % 3 = a % 3 := by omega
  have h3 : (3 * a + i) % 3 = i := by omega
  unfold xQ
  rw [h1, h2, h3]

theorem grep_xIdx {j q : ℕ} (hj : j < 2) (hq : q < 36) : GRep (xIdx j q) (xQ j q) :=
  grep_xC hj (by omega) (by omega) (by omega)

@[expose] def XS (j a : ℕ) : Subgroup GM := Subgroup.closure {xQ j (3 * a), xQ j (3 * a + 1)}

theorem XS_eq {j l m : ℕ} (hl : l < 4) (hm : m < 3) :
    XS j (3 * l + m) = Subgroup.closure {xE j l m 0, xE j l m 1} := by
  have h1 : (3 * l + m) / 3 = l := by omega
  have h2 : (3 * l + m) % 3 = m := by omega
  have e0 := xQ_eq (j := j) (a := 3 * l + m) (i := 0) (by norm_num)
  have e1 := xQ_eq (j := j) (a := 3 * l + m) (i := 1) (by norm_num)
  rw [Nat.add_zero] at e0
  rw [h1, h2] at e0 e1
  rw [XS, e0, e1]

theorem closure_pair_eq {G : Type*} [Group G] {x₀ x₁ x₂ : G} (h₀ : x₀ * x₀ = 1)
    (h₁ : x₁ * x₁ = 1) (h₀₁ : x₀ * x₁ = x₂) (h₁₀ : x₁ * x₀ = x₂) (y : ℕ → G) (hy₀ : y 0 = x₀)
    (hy₁ : y 1 = x₁) (hy₂ : y 2 = x₂) {i i' : ℕ} (hi : i < 3) (hi' : i' < 3) (hne : i ≠ i') :
    Subgroup.closure {y i, y i'} = Subgroup.closure {x₀, x₁} := by
  have hall : ∀ k < 3, y k ∈ Subgroup.closure ({x₀, x₁} : Set G) := by
    intro k hk
    interval_cases k
    · rw [hy₀]; exact Subgroup.subset_closure (Or.inl rfl)
    · rw [hy₁]; exact Subgroup.subset_closure (Or.inr rfl)
    · rw [hy₂, ← h₀₁]
      exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hall i hi
    · exact hall i' hi'
  · set S := Subgroup.closure ({y i, y i'} : Set G)
    have m0 : y i ∈ S := Subgroup.subset_closure (Or.inl rfl)
    have m1 : y i' ∈ S := Subgroup.subset_closure (Or.inr rfl)
    have e02 : x₁ = x₀ * x₂ := by rw [← h₀₁, ← mul_assoc, h₀, one_mul]
    have e20 : x₁ = x₂ * x₀ := by rw [← h₁₀, mul_assoc, h₀, mul_one]
    have e12 : x₀ = x₁ * x₂ := by rw [← h₁₀, ← mul_assoc, h₁, one_mul]
    have e21 : x₀ = x₂ * x₁ := by rw [← h₀₁, mul_assoc, h₁, mul_one]
    have key : x₀ ∈ S ∧ x₁ ∈ S := by
      interval_cases i <;> interval_cases i' <;> simp only [hy₀, hy₁, hy₂] at m0 m1 <;>
        first
        | omega
        | exact ⟨m0, m1⟩
        | exact ⟨m1, m0⟩
        | exact ⟨m0, e02 ▸ mul_mem m0 m1⟩
        | exact ⟨m1, e20 ▸ mul_mem m0 m1⟩
        | exact ⟨e12 ▸ mul_mem m0 m1, m0⟩
        | exact ⟨e21 ▸ mul_mem m0 m1, m1⟩
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact key.1
    · exact key.2

theorem XS_eq_pair {j b : ℕ} (hj : j < 2) (hb : b < 12) {i i' : ℕ} (hi : i < 3) (hi' : i' < 3)
    (hne : i ≠ i') : Subgroup.closure {xQ j (3 * b + i), xQ j (3 * b + i')} = XS j b := by
  have hm : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have e0 := xQ_eq (j := j) (a := b) (i := 0) (by norm_num)
  have e1 := xQ_eq (j := j) (a := b) (i := 1) (by norm_num)
  have e2 := xQ_eq (j := j) (a := b) (i := 2) (by norm_num)
  rw [Nat.add_zero] at e0
  rw [XS, e0, e1]
  exact closure_pair_eq (xE_sq hj hm (by norm_num)) (xE_sq hj hm (by norm_num))
    (xE_mul01 hj hm) (xE_mul10 hj hm) (fun k => xQ j (3 * b + k)) e0 e1 e2 hi hi' hne

@[expose] def cjM (g : GM) : GM →* GM where
  toFun x := g⁻¹ * x * g
  map_one' := by group
  map_mul' x y := by group

theorem cjM_mul (g h : GM) : cjM (g * h) = (cjM h).comp (cjM g) := by
  refine MonoidHom.ext fun x => ?_
  change (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h
  group

theorem map_cjM_top (g : GM) : (⊤ : Subgroup GM).map (cjM g) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ⟨g * x * g⁻¹, trivial, ?_⟩
  change g⁻¹ * (g * x * g⁻¹) * g = x
  group

@[expose] def eG (r : ℕ) : GM := ⟨eM r, eM_mem r⟩

@[expose] def regG : Array GM := Array.ofFn (n := 200) fun r => eG r.val

theorem regG_getD {r : ℕ} (hr : r < 200) : regG.getD r 1 = eG r := by
  simp [regG, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hr]

theorem grep_reg {r : ℕ} (hr : r < 200) :
    GRep (rM r) (regG.getD r 1) ∧ GRep (rIM r) (regG.getD r 1)⁻¹ := by
  rw [regG_getD hr]
  exact regOKK r hr

@[expose] def tS (j s : ℕ) : GM := wordG regG (symWd j s)

theorem sym_conj {j s q : ℕ} (hS : chkSymM j = true) (hj : j < 2) (hs : s < 2) (hq : q < 24)
    (hp : piAt j s q < 36) : cjM (tS j s) (xQ j (3 * (q / 2) + q % 2)) = xQ j (piAt j s q) := by
  unfold chkSymM at hS
  simp only [buildL_eq, bAnd_eq] at hS
  have h : symOK ((List.range 36).map (xIdx j)) j s = true := by
    interval_cases s
    · exact hS.1
    · exact hS.2
  unfold symOK at h
  simp only [strictB_eq, allN_iff] at h
  have hb := h q hq
  have hT := grep_wordC (F := rM) (FI := rIM) (R := regG) (symWd j s)
    fun l hl => grep_reg (symWd_lt j hj s hs l hl)
  have hTI := grep_wordC_inv (F := rM) (FI := rIM) (R := regG) (symWd j s)
    fun l hl => grep_reg (symWd_lt j hj s hs l hl)
  rw [nthN_map_range _ (by omega), nthN_map_range _ hp] at hb
  have hx := grep_xIdx (j := j) (q := 3 * (q / 2) + q % 2) hj (by omega)
  exact grep_eq (grep_mmul (grep_mmul hTI hx) hT) (grep_xIdx hj hp) hb

theorem σS_lt {j s a : ℕ} (hj : j < 2) (hs : s < 2) (ha : a < 12) : σS j s a < 12 := by
  have := (piAt_facts j hj s hs a ha).1
  unfold σS
  omega

theorem map_XS {j s a : ℕ} (hS : chkSymM j = true) (hj : j < 2) (hs : s < 2) (ha : a < 12) :
    (XS j a).map (cjM (tS j s)) = XS j (σS j s a) := by
  obtain ⟨h0, h1, h2, h3⟩ := piAt_facts j hj s hs a ha
  have e0 := sym_conj (q := 2 * a) hS hj hs (by omega) h0
  have e1 := sym_conj (q := 2 * a + 1) hS hj hs (by omega) h1
  have a0 : 3 * (2 * a / 2) + 2 * a % 2 = 3 * a := by omega
  have a1 : 3 * ((2 * a + 1) / 2) + (2 * a + 1) % 2 = 3 * a + 1 := by omega
  rw [a0] at e0
  rw [a1] at e1
  rw [XS, MonoidHom.map_closure, Set.image_pair, e0, e1]
  have p0 : piAt j s (2 * a) = 3 * σS j s a + piAt j s (2 * a) % 3 := by unfold σS; omega
  have p1 : piAt j s (2 * a + 1) = 3 * σS j s a + piAt j s (2 * a + 1) % 3 := by unfold σS; omega
  rw [p0, p1]
  exact XS_eq_pair hj (σS_lt hj hs ha) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h3

@[expose] def tW (j : ℕ) (w : List ℕ) : GM := (w.map (tS j)).prod

theorem map_XS_W {j : ℕ} (hS : chkSymM j = true) (hj : j < 2) :
    ∀ (w : List ℕ), (∀ s ∈ w, s < 2) → ∀ a < 12,
      (XS j a).map (cjM (tW j w)) = XS j (σW j w a) ∧ σW j w a < 12
  | [], _, a, ha => by
    refine ⟨?_, ha⟩
    have e : cjM (tW j []) = MonoidHom.id GM := by
      refine MonoidHom.ext fun x => ?_
      change (1 : GM)⁻¹ * x * 1 = x
      group
    rw [e, Subgroup.map_id]
    rfl
  | s :: w, hw, a, ha => by
    have hs := hw s List.mem_cons_self
    have ih := map_XS_W hS hj w (fun t ht => hw t (List.mem_cons_of_mem _ ht)) (σS j s a)
      (σS_lt hj hs ha)
    have e : tW j (s :: w) = tS j s * tW j w := by
      unfold tW
      rw [List.map_cons, List.prod_cons]
    refine ⟨?_, ih.2⟩
    rw [e, cjM_mul, ← Subgroup.map_map, map_XS hS hj hs ha]
    exact ih.1

theorem closure_pairY {j l₁ m₁ l₂ m₂ : ℕ} (h₁ : l₁ < 4) (hm₁ : m₁ < 3) (h₂ : l₂ < 4)
    (hm₂ : m₂ < 3) :
    Subgroup.closure (Set.range (pairY j l₁ m₁ l₂ m₂)) = XS j (3 * l₁ + m₁) ⊔ XS j (3 * l₂ + m₂) := by
  rw [XS_eq h₁ hm₁, XS_eq h₂ hm₂, ← Subgroup.closure_union]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    apply Subgroup.subset_closure
    fin_cases i
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rw [Subgroup.closure_le]
    rintro _ ((rfl | rfl) | (rfl | rfl))
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
    · exact Subgroup.subset_closure ⟨2, rfl⟩
    · exact Subgroup.subset_closure ⟨3, rfl⟩

theorem Lrow_eq {j k : ℕ} (hj : j < 2) (hk : k < 9) :
    Subgroup.closure (Set.range (lY j k)) = XS j (3 * 0 + rowAt j k 0) ⊔ XS j (3 * 1 + rowAt j k 1) :=
  closure_pairY (by norm_num) (rowAt_lt j hj k hk 0 (by norm_num)) (by norm_num)
    (rowAt_lt j hj k hk 1 (by norm_num))

theorem base_rels {j q : ℕ} (hR : chkRelM j q = true) (hj : j < 2) (hq : q < 2) :
    ∀ w ∈ l37Rels, FreeGroup.lift (pairY j (relRepF j q 0 / 3) (relRepF j q 0 % 3)
      (relRepF j q 1 / 3) (relRepF j q 1 % 3)) (FreeGroup.mk w) = 1 := by
  obtain ⟨hf0, hf1⟩ := relRep_lt j hj q hq
  set g : ℕ → GM := fun x => pairYn j (relRepF j q 0 / 3) (relRepF j q 0 % 3)
    (relRepF j q 1 / 3) (relRepF j q 1 % 3) (x % 4) with hg
  unfold chkRelM relOKM at hR
  simp only [buildL_eq, allN_iff] at hR
  have hY : ∀ t < 4, GRep (nthN ((List.range 4).map (quadX j q)) t) (g t) ∧
      GRep (nthN ((List.range 4).map (quadX j q)) t) (g t)⁻¹ := by
    intro t ht
    rw [nthN_map_range _ ht]
    have hm0 : relRepF j q 0 % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hm1 : relRepF j q 1 % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hl0 : relRepF j q 0 / 3 < 4 := by omega
    have hl1 : relRepF j q 1 / 3 < 4 := by omega
    have key : GRep (quadX j q t) (g t) := by
      interval_cases t
      · exact grep_xC (i := 0) hj hl0 hm0 (by norm_num)
      · exact grep_xC (i := 1) hj hl0 hm0 (by norm_num)
      · exact grep_xC (i := 0) hj hl1 hm1 (by norm_num)
      · exact grep_xC (i := 1) hj hl1 hm1 (by norm_num)
    refine ⟨key, grep_inv_of_sq key ?_⟩
    interval_cases t
    · exact xE_sq (i := 0) hj hm0 (by norm_num)
    · exact xE_sq (i := 1) hj hm0 (by norm_num)
    · exact xE_sq (i := 0) hj hm1 (by norm_num)
    · exact xE_sq (i := 1) hj hm1 (by norm_num)
  have hpow : ∀ r < 20, (((rootW r).map Prod.fst).map g).prod ^ relEx r = 1 := by
    intro r hr
    have hw := grep_wordF g (rootW r) fun l hl => hY l.1 ((rel_facts.2 r hr l hl).1)
    have e : ((rootW r).map fun l => if l.2 then g l.1 else (g l.1)⁻¹) =
        ((rootW r).map Prod.fst).map g := by
      rw [List.map_map]
      refine List.map_congr_left fun l hl => ?_
      rw [(rel_facts.2 r hr l hl).2]
      rfl
    rw [e] at hw
    exact grep_eq (grep_powM hw _) grep_idM (hR r hr)
  refine lift_eq_one_of_relCodes _ fun w hw => ?_
  change (w.map g).prod = 1
  rw [rel_facts.1, List.mem_map] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  rw [List.mem_range] at hr
  rw [List.map_flatten, List.map_replicate, List.prod_flatten, List.map_replicate,
    List.prod_replicate]
  exact hpow r hr

theorem lift_comp_eq_one {G H : Type*} [Group G] [Group H] (f : G →* H) (y : Fin 4 → G)
    (w : List (Fin 4 × Bool)) (h : FreeGroup.lift y (FreeGroup.mk w) = 1) :
    FreeGroup.lift (f ∘ y) (FreeGroup.mk w) = 1 := by
  have e : FreeGroup.lift (f ∘ y) = f.comp (FreeGroup.lift y) := by
    ext a
    simp
  rw [e, MonoidHom.comp_apply, h, map_one]

theorem exists_rels_pairK (hS0 : chkSymM 0 = true) (hS1 : chkSymM 1 = true)
    (hR : ∀ j < 2, ∀ q < 2, chkRelM j q = true) (j l₁ l₂ : ℕ) (hj : j < 2)
    (h₁ : l₁ < 4) (h₂ : l₂ < 4) (hl : l₁ < l₂) (m₁ m₂ : ℕ) (hm₁ : m₁ < 3) (hm₂ : m₂ < 3) :
    ∃ y : Fin 4 → GM, (∀ w ∈ l37Rels, FreeGroup.lift y (FreeGroup.mk w) = 1) ∧
      Subgroup.closure (Set.range y) = Subgroup.closure (Set.range (pairY j l₁ m₁ l₂ m₂)) := by
  have hS : chkSymM j = true := by
    interval_cases j
    · exact hS0
    · exact hS1
  set c := pairCode j l₁ l₂ m₁ m₂
  have hq : c % 2 < 2 := Nat.mod_lt _ (by norm_num)
  set q := c % 2
  set w := decWord (c / 2)
  set f0 := relRepF j q 0
  set f1 := relRepF j q 1
  obtain ⟨hf0, hf1⟩ := relRep_lt j hj q hq
  set y0 := pairY j (f0 / 3) (f0 % 3) (f1 / 3) (f1 % 3)
  refine ⟨cjM (tW j w) ∘ y0, fun r hr => lift_comp_eq_one _ _ r (base_rels (hR j hj q hq) hj hq r hr),
    ?_⟩
  have h0 := map_XS_W hS hj w (decWord_lt _) f0 hf0
  have h1 := map_XS_W hS hj w (decWord_lt _) f1 hf1
  have hy0 : Subgroup.closure (Set.range y0) = XS j f0 ⊔ XS j f1 := by
    have e := closure_pairY (j := j) (l₁ := f0 / 3) (m₁ := f0 % 3) (l₂ := f1 / 3) (m₂ := f1 % 3)
      (by omega) (Nat.mod_lt _ (by norm_num)) (by omega) (Nat.mod_lt _ (by norm_num))
    rw [Nat.div_add_mod, Nat.div_add_mod] at e
    exact e
  rw [Set.range_comp, ← MonoidHom.map_closure, hy0, Subgroup.map_sup, h0.1, h1.1,
    closure_pairY h₁ hm₁ h₂ hm₂]
  rcases pairW_facts j hj l₁ h₁ l₂ h₂ m₁ hm₁ m₂ hm₂ with hle | ⟨e0, e1⟩ | ⟨e0, e1⟩
  · omega
  · rw [e0, e1]
  · rw [e0, e1, sup_comm]

theorem size_toArray_map (n : ℕ) (g : ℕ → GM) : ((List.range n).map g).toArray.size = n := by
  simp

theorem getD_toArray_map {n r : ℕ} (g : ℕ → GM) (hr : r < n) :
    ((List.range n).map g).toArray.getD r 1 = g r := by
  simp [Array.getD_eq_getD_getElem?, hr]

theorem getD_toArray_map_ge {n r : ℕ} (g : ℕ → GM) (hr : n ≤ r) :
    ((List.range n).map g).toArray.getD r 1 = 1 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none, hr]

theorem mem_toArray_map {n : ℕ} (g : ℕ → GM) {K : Subgroup GM} (h : ∀ r < n, g r ∈ K) (k : ℕ) :
    ((List.range n).map g).toArray.getD k 1 ∈ K := by
  by_cases hk : k < n
  · rw [getD_toArray_map g hk]
    exact h k hk
  · rw [getD_toArray_map_ge g (not_lt.1 hk)]
    exact K.one_mem

theorem crep_map {n : ℕ} (f : ℕ → ℕ) (g : ℕ → GM) (h : ∀ r < n, GRep (f r) (g r))
    (hsq : ∀ r < n, g r * g r = 1) :
    CRep ((List.range n).map f) ((List.range n).map f) ((List.range n).map g).toArray := by
  refine ⟨by simp, by simp, fun r hr => ?_⟩
  rw [size_toArray_map] at hr
  rw [nthN_map_range f hr, getD_toArray_map g hr]
  exact ⟨h r hr, grep_inv_of_sq (h r hr) (hsq r hr)⟩

@[expose] def inE (j q : ℕ) : GM := xE j (q / 2) (rowAt j 0 (q / 2)) (q % 2)

theorem grep_inX {j q : ℕ} (hj : j < 2) (hq : q < 8) : GRep (inX j q) (inE j q) :=
  grep_xC (l := q / 2) (m := rowAt j 0 (q / 2)) (i := q % 2) hj (by omega)
    (rowAt_lt j hj 0 (by norm_num) _ (by omega)) (by omega)

theorem inE_sq {j q : ℕ} (hj : j < 2) (hq : q < 8) : inE j q * inE j q = 1 :=
  xE_sq hj (rowAt_lt j hj 0 (by norm_num) _ (by omega)) (by omega)

theorem inE_mem {j q : ℕ} (hq : q < 4) : inE j q ∈ Subgroup.closure (Set.range (lY j 0)) := by
  interval_cases q
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩
  · exact Subgroup.subset_closure ⟨3, rfl⟩

theorem base_in {j : ℕ} (hI : chkInM j = true) (hj : j < 2) (i : ℕ) (hi : i < 4) :
    xE j (2 + i / 2) (rowAt j 0 (2 + i / 2)) (i % 2) ∈ Subgroup.closure (Set.range (lY j 0)) := by
  unfold chkInM at hI
  simp only [buildL_eq, runK_spec, allN_iff] at hI
  obtain ⟨hp, ht, -⟩ := prog_facts j hj
  have hc := grep_inX (j := j) (q := 4 + i) hj (by omega)
  have h0 := crep_map (n := 4) (inX j) (inE j) (fun r hr => grep_inX hj (by omega))
    (fun r hr => inE_sq hj (by omega))
  have hm := slp_spec (prog := inProg j) h0 (by rw [size_toArray_map]; exact hp)
    (mem_toArray_map (inE j) fun r hr => inE_mem hr) (by rw [size_toArray_map]; exact ht i hi)
    hc (hI i hi)
  have e : inE j (4 + i) = xE j (2 + i / 2) (rowAt j 0 (2 + i / 2)) (i % 2) := by
    have a1 : (4 + i) / 2 = 2 + i / 2 := by omega
    have a2 : (4 + i) % 2 = i % 2 := by omega
    unfold inE
    rw [a1, a2]
  rw [← e]
  exact hm

theorem XS_le_of_mem {j l m : ℕ} (hl : l < 4) (hm : m < 3) {K : Subgroup GM}
    (h0 : xE j l m 0 ∈ K) (h1 : xE j l m 1 ∈ K) : XS j (3 * l + m) ≤ K := by
  rw [XS_eq hl hm, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact h0
  · exact h1

theorem rowIdx_lt {j k l : ℕ} (hj : j < 2) (hk : k < 9) (hl : l < 4) :
    3 * l + rowAt j k l < 12 := by
  have := rowAt_lt j hj k hk l hl
  omega

theorem XS_le_Lrow {j k l : ℕ} (hS : chkSymM j = true) (hI : chkInM j = true) (hj : j < 2)
    (hk : k < 9) (hl : l < 4) : XS j (3 * l + rowAt j k l) ≤ Subgroup.closure (Set.range (lY j k)) := by
  have hr := fun (k' l' : ℕ) (hk' : k' < 9) (hl' : l' < 4) => rowAt_lt j hj k' hk' l' hl'
  have b2 : XS j (3 * 2 + rowAt j 0 2) ≤ Subgroup.closure (Set.range (lY j 0)) :=
    XS_le_of_mem (by norm_num) (hr 0 2 (by norm_num) (by norm_num))
      (base_in hI hj 0 (by norm_num)) (base_in hI hj 1 (by norm_num))
  have b3 : XS j (3 * 3 + rowAt j 0 3) ≤ Subgroup.closure (Set.range (lY j 0)) :=
    XS_le_of_mem (by norm_num) (hr 0 3 (by norm_num) (by norm_num))
      (base_in hI hj 2 (by norm_num)) (base_in hI hj 3 (by norm_num))
  set w := inWd j k
  have hw : ∀ s ∈ w, s < 2 := decWord_lt _
  have m := fun (a : ℕ) (ha : a < 12) => (map_XS_W hS hj w hw a ha).1
  have hmap : (Subgroup.closure (Set.range (lY j 0))).map (cjM (tW j w)) = Subgroup.closure (Set.range (lY j k)) := by
    rw [Lrow_eq hj (by norm_num), Subgroup.map_sup, m _ (rowIdx_lt hj (by norm_num) (by norm_num)),
      m _ (rowIdx_lt hj (by norm_num) (by norm_num)), Lrow_eq hj hk]
    rcases (inW_facts j hj k hk).1 with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · rw [e0, e1]
    · rw [e0, e1, sup_comm]
  have i2 := Subgroup.map_mono (f := cjM (tW j w)) b2
  have i3 := Subgroup.map_mono (f := cjM (tW j w)) b3
  rw [m _ (rowIdx_lt hj (by norm_num) (by norm_num)), hmap] at i2 i3
  rw [Lrow_eq hj hk]
  interval_cases l
  · exact le_sup_left
  · exact le_sup_right
  · rw [← Lrow_eq hj hk]
    rcases (inW_facts j hj k hk).2 with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · rw [e0] at i2; exact i2
    · rw [e1] at i3; exact i3
  · rw [← Lrow_eq hj hk]
    rcases (inW_facts j hj k hk).2 with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · rw [e1] at i3; exact i3
    · rw [e0] at i2; exact i2

theorem mem_closure_inK (hS0 : chkSymM 0 = true) (hS1 : chkSymM 1 = true)
    (hI : ∀ j < 2, chkInM j = true) (j k : ℕ) (hj : j < 2) (hk : k < 9) (i : ℕ) (hi : i < 4) :
    xE j (2 + i / 2) (rowAt j k (2 + i / 2)) (i % 2) ∈ Subgroup.closure (Set.range (lY j k)) := by
  have hS : chkSymM j = true := by
    interval_cases j
    · exact hS0
    · exact hS1
  have hm := rowAt_lt j hj k hk (2 + i / 2) (by omega)
  refine XS_le_Lrow hS (hI j hj) hj hk (l := 2 + i / 2) (by omega) ?_
  rw [XS_eq (by omega) hm]
  apply Subgroup.subset_closure
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h]; exact Or.inl rfl
  · rw [h]; exact Or.inr rfl

theorem M_le_of_gM_mem (K : Subgroup Mat45ˣ) (h : ∀ k : Fin 8, gM k ∈ K) : M ≤ K := by
  rintro _ ⟨u, rfl⟩
  have hu : u ∈ Subgroup.closure (Set.range (PresentedGroup.of : Fin 8 → FHat 1 1 1)) := by
    rw [PresentedGroup.closure_range_of]; trivial
  induction hu using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    rw [psiM_of]; exact h k
  | one => rw [map_one]; exact K.one_mem
  | mul x y _ _ hx hy => rw [map_mul]; exact K.mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact K.inv_mem hx

theorem eq_top_of_eG_mem {S : Subgroup GM} (h : ∀ i < 8, eG i ∈ S) : S = ⊤ := by
  have hK := M_le_of_gM_mem (S.map M.subtype) fun k => ⟨eG k.val, h k.val k.isLt,
    eM_gen k⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hK x.2
  have e : y = x := Subtype.ext hyx
  rwa [e] at hy

@[expose] def topE (j q : ℕ) : GM :=
  if q < 4 then inE j q else xE j (topBL j) (topBM j) (q - 4)

theorem grep_topX {j q : ℕ} (hj : j < 2) (hq : q < 6) : GRep (topX j q) (topE j q) := by
  obtain ⟨-, -, -, -, hL, hM⟩ := prog_facts j hj
  have e : topX j q = if Nat.blt 3 q = true then xC j (topBL j) (topBM j) (q - 4) else inX j q :=
    nIf_eq _ _ _
  rw [e, topE]
  by_cases h : q < 4
  · have hb : ¬ Nat.blt 3 q = true := by rw [Nat.blt_eq]; omega
    rw [if_neg hb, if_pos h]
    exact grep_inX hj (by omega)
  · have hb : Nat.blt 3 q = true := by rw [Nat.blt_eq]; omega
    rw [if_pos hb, if_neg h]
    exact grep_xC hj hL hM (by omega)

theorem topE_sq {j q : ℕ} (hj : j < 2) (hq : q < 6) : topE j q * topE j q = 1 := by
  obtain ⟨-, -, -, -, -, hM⟩ := prog_facts j hj
  unfold topE
  by_cases h : q < 4
  · rw [if_pos h]
    exact inE_sq hj (by omega)
  · rw [if_neg h]
    exact xE_sq hj hM (by omega)

theorem base_top {j : ℕ} (hT : chkTopM j = true) (hj : j < 2) :
    Subgroup.closure (Set.range (lY j 0)) ⊔ XS j (3 * topBL j + topBM j) = ⊤ := by
  unfold chkTopM at hT
  simp only [buildL_eq, runK_spec, allN_iff] at hT
  obtain ⟨-, -, hp, ht, hL, hM⟩ := prog_facts j hj
  set S := Subgroup.closure (Set.range (lY j 0)) ⊔ XS j (3 * topBL j + topBM j)
  have hx : XS j (3 * topBL j + topBM j) ≤ S := le_sup_right
  rw [XS_eq hL hM] at hx
  have hl : Subgroup.closure (Set.range (lY j 0)) ≤ S := le_sup_left
  have hK : ∀ r < 6, topE j r ∈ S := by
    intro r hr
    unfold topE
    by_cases h : r < 4
    · rw [if_pos h]
      exact hl (inE_mem h)
    · rw [if_neg h]
      have h' : r - 4 = 0 ∨ r - 4 = 1 := by omega
      rcases h' with h' | h'
      · rw [h']; exact hx (Subgroup.subset_closure (Or.inl rfl))
      · rw [h']; exact hx (Subgroup.subset_closure (Or.inr rfl))
  have h0 := crep_map (n := 6) (topX j) (topE j) (fun r hr => grep_topX hj hr)
    (fun r hr => topE_sq hj hr)
  refine eq_top_of_eG_mem fun i hi => ?_
  exact slp_spec (prog := topProg j) h0 (by rw [size_toArray_map]; exact hp)
    (mem_toArray_map (topE j) hK) (by rw [size_toArray_map]; exact ht i hi)
    (regOKK i (by omega)).1 (hT i hi)

theorem closure_topK (hS0 : chkSymM 0 = true) (hS1 : chkSymM 1 = true)
    (hI : ∀ j < 2, chkInM j = true) (hT : ∀ j < 2, chkTopM j = true) (j k l m : ℕ)
    (hj : j < 2) (hk : k < 9) (hl : l < 4) (hm : m < 3) (hne : m ≠ rowAt j k l) :
    Subgroup.closure (Set.range (lY j k) ∪ {xE j l m 0, xE j l m 1}) = (⊤ : Subgroup GM) := by
  have hS : chkSymM j = true := by
    interval_cases j
    · exact hS0
    · exact hS1
  obtain ⟨-, -, -, -, hL, hM⟩ := prog_facts j hj
  rw [Subgroup.closure_union, ← XS_eq hl hm]
  obtain ⟨e0, ⟨l₀, hl₀, f0⟩, ⟨l₁, hl₁, f1⟩⟩ := (topW_facts j hj k hk l hl m hm).resolve_left hne
  set w := topWd j k l m
  have hw : ∀ s ∈ w, s < 2 := decWord_lt _
  have mp := fun (a : ℕ) (ha : a < 12) => (map_XS_W hS hj w hw a ha).1
  have hb := congrArg (Subgroup.map (cjM (tW j w))) (base_top (hT j hj) hj)
  rw [map_cjM_top, Subgroup.map_sup, Lrow_eq hj (by norm_num), Subgroup.map_sup,
    mp _ (rowIdx_lt hj (by norm_num) (by norm_num)), mp _ (rowIdx_lt hj (by norm_num) (by norm_num)),
    mp _ (by omega), e0, f0, f1] at hb
  rw [eq_top_iff, ← hb]
  refine sup_le_sup (sup_le (XS_le_Lrow hS (hI j hj) hj hk hl₀) (XS_le_Lrow hS (hI j hj) hj hk hl₁))
    le_rfl

end Model

end CertificateChecks.KernelMisc.ON.L37
