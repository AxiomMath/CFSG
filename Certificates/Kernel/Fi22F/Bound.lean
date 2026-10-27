module

public import Certificates.Kernel.Fi22F.Words
public import Certificates.Kernel.Fi22F.WalkChecks
public import Certificates.Kernel.Fi22F.TabS
public import Certificates.Kernel.Fi22F.TabH
public import Certificates.Kernel.Fi22F.Three

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceJson CFSG.Certificates CFSG.Certificates.LCE CFSG.KC.Fi22F.Walks
  CFSG.Sporadic.Presentation.Fi22Exact CertificateChecks.KernelCo2 CertificateChecks.KernelFi22

abbrev relsF : Set (FreeGroup (Fin 6)) := {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk}

noncomputable abbrev gen : ℕ → FG := pgen relsF

theorem of_sq (i : Fin 6) : (PresentedGroup.of i : FG) * PresentedGroup.of i = 1 := by
  have h : FreeGroup.mk [(i, true), (i, true)] ∈ relsF := by
    simp only [Set.mem_setOf_eq, List.mem_map, wsF, List.mem_append]
    exact ⟨[(i, true), (i, true)], Or.inl ⟨i, List.mem_finRange i, rfl⟩, rfl⟩
  have := PresentedGroup.one_of_mem h
  rw [← this]
  rfl

theorem gen_lt {g : ℕ} (h : g < 6) : gen g = PresentedGroup.of ⟨g, h⟩ := pgen_lt relsF h

theorem gen_sq (g : ℕ) : gen g * gen g = 1 := by
  by_cases h : g < 6
  · rw [gen_lt h]
    exact of_sq _
  · have e : gen g = 1 := by simp [pgen, h]
    rw [e, one_mul]

theorem gen_inv (g : ℕ) : (gen g)⁻¹ = gen g := inv_eq_of_mul_eq_one_right (gen_sq g)

noncomputable def V (l : List ℕ) : FG := (l.map gen).prod

theorem V_append (l l' : List ℕ) : V (l ++ l') = V l * V l' := by
  simp [V, List.map_append, List.prod_append]

theorem V_cons (g : ℕ) (l : List ℕ) : V (g :: l) = gen g * V l := by
  simp [V]

theorem V_reverse (l : List ℕ) : V l.reverse = (V l)⁻¹ := by
  unfold V
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map]
  congr 2
  apply List.map_congr_left
  intro g _
  exact (gen_inv g).symm

noncomputable def T (x : FG) : FG := x⁻¹ * gen 0 * x

theorem V_Ew (c : List ℕ) : V (Ew c) = T (V c) := by
  unfold Ew T
  rw [V_append, V_cons, V_reverse]
  group

theorem T_sq (x : FG) : T x * T x = 1 := by
  unfold T
  calc x⁻¹ * gen 0 * x * (x⁻¹ * gen 0 * x) = x⁻¹ * (gen 0 * gen 0) * x := by group
    _ = 1 := by rw [gen_sq]; group

noncomputable abbrev Cen : Subgroup FG := Subgroup.centralizer {gen 0}

theorem T_eq {x y : FG} (h : x * y⁻¹ ∈ Cen) : T x = T y := by
  rw [Subgroup.mem_centralizer_iff] at h
  have h' := h (gen 0) rfl
  unfold T
  have e : gen 0 * x = x * y⁻¹ * gen 0 * y := by
    calc gen 0 * x = gen 0 * (x * y⁻¹) * y := by group
      _ = x * y⁻¹ * gen 0 * y := by rw [h']
  calc x⁻¹ * gen 0 * x = x⁻¹ * (gen 0 * x) := by group
    _ = x⁻¹ * (x * y⁻¹ * gen 0 * y) := by rw [e]
    _ = y⁻¹ * gen 0 * y := by group

theorem letV_pos (g : ℕ) : letV gen (2 * g) = gen g := by
  unfold letV
  have h1 : ¬ 2 * g = 255 := by omega
  simp only [h1, ↓reduceIte, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem pos_lt {l : List ℕ} (h : ∀ g ∈ l, g < 6) : ∀ c ∈ pos l, c < 256 := by
  intro c hc
  simp only [pos, List.mem_map] at hc
  obtain ⟨g, hg, rfl⟩ := hc
  have := h g hg
  change 2 * g < 256
  omega

theorem map_pos (l : List ℕ) : (pos l).map (letV gen) = l.map gen := by
  simp only [pos, List.map_map]
  apply List.map_congr_left
  intro g _
  exact letV_pos g

theorem bval_posL {l : List ℕ} (hl : l.length < 1024) (h : ∀ g ∈ l, g < 6) :
    bval gen (wWord (entL (pos l))) (wLen (entL (pos l))) = V l := by
  rw [bval_entL gen (pos l) (by simpa [pos] using hl) (pos_lt h), map_pos]
  rfl

theorem bval_posW {l : List ℕ} (hl : l.length < 1024) (h : ∀ g ∈ l, g < 6) :
    bval gen (wWord (entW (pos l))) (wLen (entW (pos l))) = V l := by
  rw [bval_entW gen (pos l) (by simpa [pos] using hl) (pos_lt h), map_pos]
  rfl

theorem code_lt (p : Fin 6 × Bool) : code p < 12 := by
  obtain ⟨i, b⟩ := p
  have := i.isLt
  cases b
  · change 2 * i.val + 1 < 12
    omega
  · change 2 * i.val + 0 < 12
    omega

theorem letV_code (p : Fin 6 × Bool) :
    letV gen (code p) = cond p.2 (PresentedGroup.of p.1) (PresentedGroup.of p.1)⁻¹ := by
  obtain ⟨i, b⟩ := p
  have hi := i.isLt
  unfold letV
  cases b
  · have e : code (i, false) = 2 * i.val + 1 := rfl
    have h1 : ¬ 2 * i.val + 1 = 255 := by omega
    have h2 : ¬ (2 * i.val + 1) % 2 = 0 := by omega
    have h3 : (2 * i.val + 1) / 2 = i.val := by omega
    rw [e]
    simp only [h1, h2, h3, ↓reduceIte, cond_false]
    rw [gen_lt hi]
  · have e : code (i, true) = 2 * i.val := by
      change 2 * i.val + 0 = _
      rfl
    have h1 : ¬ 2 * i.val = 255 := by omega
    rw [e]
    simp only [h1, ↓reduceIte, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
      cond_true]
    rw [gen_lt hi]

theorem mk_eq_lift (x : FreeGroup (Fin 6)) :
    PresentedGroup.mk relsF x = FreeGroup.lift (PresentedGroup.of (rels := relsF)) x := by
  have h : PresentedGroup.mk relsF = FreeGroup.lift (PresentedGroup.of (rels := relsF)) := by
    apply FreeGroup.ext_hom
    intro a
    rw [FreeGroup.lift_apply_of]
    rfl
  rw [h]

theorem word_val (w : List (Fin 6 × Bool)) :
    ((w.map code).map (letV gen)).prod = PresentedGroup.mk relsF (FreeGroup.mk w) := by
  rw [mk_eq_lift, FreeGroup.lift_mk, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact letV_code p

theorem rel_val {w : List (Fin 6 × Bool)} (hw : w ∈ wsF) :
    ((w.map code).map (letV gen)).prod = 1 := by
  rw [word_val]
  exact PresentedGroup.one_of_mem (List.mem_map.2 ⟨w, hw, rfl⟩)

theorem relsLt_spec {ws : List (List (Fin 6 × Bool))} (h : relsLt ws = true) :
    ∀ w ∈ ws, w.length < 1024 := by
  induction ws with
  | nil => intro w hw; cases hw
  | cons v ws ih =>
    have h' : andB (Nat.blt v.length 1024) (relsLt ws) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact Nat.le_of_ble_eq_true h1
    · exact ih h2 w hw

theorem wordsLt_spec {ws : List (List ℕ)} (h : wordsLt ws = true) :
    ∀ w ∈ ws, (∀ g ∈ w, g < 6) ∧ w.length < 1024 := by
  induction ws with
  | nil => intro w hw; cases hw
  | cons v ws ih =>
    have h' : andB (andB (lt6 v) (Nat.blt v.length 1024)) (wordsLt ws) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    obtain ⟨h3, h4⟩ := (andB_eq' _ _).1 h1
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨lt6_spec h3, Nat.le_of_ble_eq_true h4⟩
    · exact ih h2 w hw

theorem relsRT {RT : ℕ → ℕ} (h : relsBind RT wsF 0 = true) :
    ∀ r < 204, bval gen (wWord (RT r)) (wLen (RT r)) = 1 := by
  intro r hr
  have hl : r < wsF.length := by rw [lens.1]; exact hr
  have e := relsBind_spec h r hl
  rw [Nat.zero_add] at e
  have hm : wsF.getD r [] ∈ wsF := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hlen := relsLt_spec rels_lt _ hm
  rw [e, bval_entL gen _ (by simpa using hlen) (fun c hc => by
    simp only [List.mem_map] at hc
    obtain ⟨p, -, rfl⟩ := hc
    have := code_lt p
    omega)]
  exact rel_val hm

theorem lift_conjW (i : Fin 6) (c : List (Fin 6)) :
    FreeGroup.lift (PresentedGroup.of (rels := relsF)) (FreeGroup.mk (conjW i c)) =
      (c.map PresentedGroup.of).prod⁻¹ * PresentedGroup.of i * (c.map PresentedGroup.of).prod := by
  unfold conjW
  rw [FreeGroup.lift_mk]
  simp only [List.map_append, List.prod_append, List.map_map, List.map_reverse]
  simp [Function.comp_def, List.prod_inv_reverse]

theorem V_val (c : List (Fin 6)) : V (c.map (·.val)) = (c.map (PresentedGroup.of (rels := relsF))).prod := by
  unfold V
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact pgen_lt relsF i.isLt

theorem qrel_eq {q : Fin 6 × List (Fin 6) × Fin 6 × List (Fin 6)} (hq : q ∈ qrels) :
    (V (q.2.1.map (·.val)))⁻¹ * PresentedGroup.of q.1 * V (q.2.1.map (·.val)) =
      (V (q.2.2.2.map (·.val)))⁻¹ * PresentedGroup.of q.2.2.1 * V (q.2.2.2.map (·.val)) := by
  have hm : FreeGroup.mk (qWord q) ∈ relsF :=
    List.mem_map.2 ⟨qWord q, List.mem_append_right _ (List.mem_map.2 ⟨q, hq, rfl⟩), rfl⟩
  have h1 := PresentedGroup.one_of_mem hm
  rw [mk_eq_lift] at h1
  unfold qWord at h1
  rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv, lift_conjW, lift_conjW,
    mul_inv_eq_one] at h1
  rw [V_val, V_val]
  exact h1

theorem sWords_cen : ∀ x ∈ sWords, V x ∈ Cen := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    simp [V]
  · simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨q, ⟨hq, h1, h2⟩, rfl⟩ := hx
    have e := qrel_eq hq
    have h0 : (PresentedGroup.of q.1 : FG) = gen 0 := by
      rw [show q.1 = ⟨0, by norm_num⟩ from Fin.ext h1, ← pgen_lt relsF (by norm_num : 0 < 6)]
    have h0' : (PresentedGroup.of q.2.2.1 : FG) = gen 0 := by
      rw [show q.2.2.1 = ⟨0, by norm_num⟩ from Fin.ext h2, ← pgen_lt relsF (by norm_num : 0 < 6)]
    rw [h0, h0'] at e
    rw [V_append, V_reverse]
    set a := V (q.2.1.map (·.val))
    set b := V (q.2.2.2.map (·.val))
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    calc gen 0 * (a * b⁻¹) = a * (a⁻¹ * gen 0 * a) * b⁻¹ := by group
      _ = a * (b⁻¹ * gen 0 * b) * b⁻¹ := by rw [e]
      _ = a * b⁻¹ * gen 0 := by group

theorem factsOk_of_lceOk {blk WT RT ST LVs : ℕ → ℕ} {INV INV8 L nC nCl mLV a m Hs nR nS nf : ℕ}
    {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}
    (h : lceOk blk WT RT ST LVs INV INV8 L nC nCl mLV a m Hs nR nS nf Cs CCs S0 S1 X0 X1 = true) :
    HO.factsOk blk WT RT ST INV INV8 L nC m Hs nR nS nf S0 S1 Cs = true := by
  unfold lceOk at h
  obtain ⟨h1, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h2, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h3, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨-, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨-, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h6, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h7, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h8, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h9, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h10, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h11, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h12, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨h13, -⟩ := (andB_eq' _ _).1 h
  unfold HO.factsOk
  rw [h1, h2, h3, h8, h9, h10, h6, h7, h11, h13, h12]
  rfl

theorem walk_cen : ∀ (l : List ℕ) (R : ℕ), (∀ g ∈ l, g < 6) →
    wk (sel2 CFSG.KD.FiFS.B) CFSG.KD.FiFS.nf l R = true → V l ∈ Cen := by
  have hf := factsOk_of_lceOk tabS_ok
  have hST : ∀ j < 73, bval gen (wWord (sel1 CFSG.KD.FiFS.ST j)) (wLen (sel1 CFSG.KD.FiFS.ST j)) ∈ Cen := by
    intro j hj
    have hl : j < sWords.length := by rw [lens.2.1]; exact hj
    have e := posBind_spec stS_bind j hl
    rw [Nat.zero_add] at e
    have hm : sWords.getD j [] ∈ sWords := by
      rw [List.getD_eq_getElem _ _ hl]
      exact List.getElem_mem hl
    obtain ⟨h6, hlen⟩ := wordsLt_spec sWords_lt _ hm
    rw [e, bval_posL hlen h6]
    exact sWords_cen _ hm
  obtain ⟨rep, h0, hw⟩ := HO.walkTo_sound gen Cen hf (relsRT relsS_bind) hST
  intro l R h6 hk
  have hk' : andB (Nat.blt l.length 1024) (CFSG.KC.HOrb.walkTo (sel2 CFSG.KD.FiFS.B) CFSG.KD.FiFS.nf (entW (pos l)) 0 R 0)
    = true := hk
  obtain ⟨hlen, hwk⟩ := (andB_eq' _ _).1 hk'
  have := hw _ 0 R 0 (by norm_num) hwk
  rw [h0, one_mul, inv_one, mul_one, bval_posW (Nat.le_of_ble_eq_true hlen) h6] at this
  exact this

noncomputable abbrev cs : List (List ℕ) := CFSG.KD.FiFW.cs

noncomputable def u (g : ℕ) : FG := T (V (cs.getD g []))

theorem u_sq (g : ℕ) : u g * u g = 1 := T_sq _

theorem u_inv (g : ℕ) : (u g)⁻¹ = u g := inv_eq_of_mul_eq_one_right (u_sq g)

theorem cs_lt (g : ℕ) : ∀ x ∈ cs.getD g [], x < 6 := by
  intro x hx
  by_cases hg : g < cs.length
  · rw [List.getD_eq_getElem _ _ hg] at hx
    exact csOK_spec cs_ok _ (List.getElem_mem hg) x hx
  · rw [List.getD_eq_default _ _ (by omega)] at hx
    cases hx

theorem V_flatMap (w : List ℕ) : V (w.flatMap fun g => Ew (cs.getD g [])) = (w.map u).prod := by
  induction w with
  | nil => rfl
  | cons g w ih => rw [List.flatMap_cons, V_append, ih, V_Ew, List.map_cons, List.prod_cons]; rfl

theorem V_pW (i : ℕ) (w : List ℕ) : V (pW cs i w) = V (cs.getD i []) * (w.map u).prod := by
  unfold pW
  rw [V_append, V_flatMap]

theorem lt6_pW {i : ℕ} {w : List ℕ} (hw : ∀ g ∈ w, g < 6) : ∀ x ∈ pW cs i w, x < 6 := by
  intro x hx
  simp only [pW, List.mem_append, List.mem_flatMap, Ew, List.mem_cons, List.mem_reverse] at hx
  rcases hx with hx | ⟨g, -, hx | rfl | hx⟩
  · exact cs_lt i x hx
  · exact cs_lt g x hx
  · norm_num
  · exact cs_lt g x hx

theorem lt6_Ew {c : List ℕ} (hc : ∀ x ∈ c, x < 6) : ∀ x ∈ Ew c, x < 6 := by
  intro x hx
  simp only [Ew, List.mem_append, List.mem_cons, List.mem_reverse] at hx
  rcases hx with hx | rfl | hx
  · exact hc x hx
  · norm_num
  · exact hc x hx

theorem T_mul (x y : FG) : T (x * y) = y⁻¹ * T x * y := by
  unfold T
  group

theorem rel2 {t v : FG} (ht : t * t = 1) (hv : v * v = 1) (h : v⁻¹ * t * v = t) : (t * v) ^ 2 = 1 := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  rw [hv'] at h
  calc (t * v) ^ 2 = t * (v * t * v) := by rw [pow_two]; group
    _ = 1 := by rw [h, ht]

theorem rel3 {t v : FG} (ht : t * t = 1) (hv : v * v = 1) (h : v⁻¹ * t * v = t⁻¹ * v * t) :
    (t * v) ^ 3 = 1 := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [hv', ht'] at h
  calc (t * v) ^ 3 = t * (v * t * v) * t * v := by rw [pow_succ, pow_two]; group
    _ = t * (t * v * t) * t * v := by rw [h]
    _ = (t * t) * v * (t * t) * v := by group
    _ = 1 := by rw [ht, one_mul, mul_one, hv]

noncomputable def U (k : ℕ) : FG := if k < 6 then u k else 1

theorem letV_U_pos {g : ℕ} (hg : g < 6) : letV U (2 * g) = u g := by
  unfold letV
  have h1 : ¬ 2 * g = 255 := by omega
  simp only [h1, ↓reduceIte, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), U, hg]

theorem letV_U_neg {g : ℕ} (hg : g < 6) : letV U (2 * g + 1) = (u g)⁻¹ := by
  unfold letV
  have h1 : ¬ 2 * g + 1 = 255 := by omega
  have h2 : ¬ (2 * g + 1) % 2 = 0 := by omega
  have h3 : (2 * g + 1) / 2 = g := by omega
  simp only [h1, h2, h3, ↓reduceIte, U, hg]

theorem xrL_val {i j m : ℕ} {w : List ℕ} (hi : i < 6) (hj : j < 6) (hw : ∀ g ∈ w, g < 6) :
    ((xrL i w j m).map (letV U)).prod = ((w.map u).prod⁻¹ * u i * (w.map u).prod * u j) ^ m := by
  unfold xrL
  rw [List.map_flatten, List.map_replicate, List.prod_flatten, List.map_replicate, List.prod_replicate]
  congr 1
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, List.map_map]
  rw [letV_U_pos hi, letV_U_pos hj]
  have e1 : (List.map (letV U ∘ fun g => 2 * g + 1) w.reverse).prod = (w.map u).prod⁻¹ := by
    rw [List.prod_inv_reverse, List.map_reverse, List.map_map]
    congr 2
    apply List.map_congr_left
    intro g hg
    exact letV_U_neg (hw g hg)
  have e2 : (List.map (letV U ∘ fun g => 2 * g) w).prod = (w.map u).prod := by
    congr 1
    apply List.map_congr_left
    intro g hg
    exact letV_U_pos (hw g hg)
  rw [e1, e2]

theorem xrL_lt {i j m : ℕ} {w : List ℕ} (hi : i < 6) (hj : j < 6) (hw : ∀ g ∈ w, g < 6) :
    ∀ c ∈ xrL i w j m, c < 256 := by
  intro c hc
  unfold xrL at hc
  rw [List.mem_flatten] at hc
  obtain ⟨s, hs, hc⟩ := hc
  rw [(List.mem_replicate.1 hs).2] at hc
  simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_singleton] at hc
  rcases hc with ((⟨g, hg, rfl⟩ | rfl) | ⟨g, hg, rfl⟩) | rfl
  · have := hw g hg; omega
  · omega
  · have := hw g hg; omega
  · omega

theorem xr_val {r : ℕ} (hr : r < 27) :
    bval U (wWord (CFSG.KD.Fi22KM.XRs r)) (wLen (CFSG.KD.Fi22KM.XRs r)) = 1 := by
  have hl : r < CFSG.KD.FiFW.pairs.length := by rw [lens.2.2.2.1]; exact hr
  have h := pairsOK_spec pairs_ok r hl
  rw [Nat.zero_add] at h
  set pr := CFSG.KD.FiFW.pairs.getD r (0, [], 0, 0, 0)
  obtain ⟨i, w, j, m, R⟩ := pr
  unfold pairOK at h
  dsimp only at h
  obtain ⟨hX, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨hlen, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨hi, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨hj, h⟩ := (andB_eq' _ _).1 h
  obtain ⟨hw, h⟩ := (andB_eq' _ _).1 h
  have hi' : i < 6 := Nat.le_of_ble_eq_true hi
  have hj' : j < 6 := Nat.le_of_ble_eq_true hj
  have hw' := lt6_spec hw
  rw [Nat.eq_of_beq_eq_true hX, bval_entL U _ (Nat.le_of_ble_eq_true hlen) (xrL_lt hi' hj' hw'),
    xrL_val hi' hj' hw']
  set W := (w.map u).prod
  have hP : T (V (pW cs i w)) = W⁻¹ * u i * W := by
    rw [V_pW, T_mul]
    rfl
  have ht : W⁻¹ * u i * W * (W⁻¹ * u i * W) = 1 := by
    calc W⁻¹ * u i * W * (W⁻¹ * u i * W) = W⁻¹ * (u i * u i) * W := by group
      _ = 1 := by rw [u_sq]; group
  have hp6 := lt6_pW (i := i) hw'
  have hcj := cs_lt j
  by_cases m1 : m = 1
  · subst m1
    rw [Nat.beq_refl] at h
    obtain ⟨hij, hwl⟩ := (andB_eq' _ _).1 h
    have hw0 : W = 1 := by
      change (w.map u).prod = 1
      rw [List.length_eq_zero_iff.mp (Nat.eq_of_beq_eq_true hwl)]
      rfl
    rw [← Nat.eq_of_beq_eq_true hij, hw0, pow_one, inv_one, one_mul, mul_one, u_sq]
  have hm1 : Nat.beq m 1 = false := by
    cases hb : Nat.beq m 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) m1
  rw [hm1] at h
  by_cases m2 : m = 2
  · subst m2
    have h2 : wk (sel2 CFSG.KD.FiFS.B) CFSG.KD.FiFS.nf (walk2 cs i w j) R = true := h
    have hc := walk_cen _ R (by
      intro x hx
      simp only [walk2, List.mem_append, List.mem_reverse] at hx
      rcases hx with (hx | hx) | hx
      · exact hp6 x hx
      · exact lt6_Ew hcj x hx
      · exact hp6 x hx) h2
    rw [walk2, V_append, V_append, V_reverse, V_Ew] at hc
    have e := T_eq hc
    rw [T_mul, hP] at e
    exact rel2 ht (u_sq j) e
  have hm2 : Nat.beq m 2 = false := by
    cases hb : Nat.beq m 2
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) m2
  rw [hm2] at h
  have h3 : andB (Nat.beq m 3) (wk (sel2 CFSG.KD.FiFS.B) CFSG.KD.FiFS.nf (walk3 cs i w j) R) = true := h
  obtain ⟨hm3, h4⟩ := (andB_eq' _ _).1 h3
  obtain rfl : m = 3 := Nat.eq_of_beq_eq_true hm3
  have hc := walk_cen _ R (by
    intro x hx
    simp only [walk3, List.mem_append, List.mem_reverse] at hx
    rcases hx with (hx | hx) | hx | hx
    · exact hp6 x hx
    · exact lt6_Ew hcj x hx
    · exact hcj x hx
    · exact lt6_Ew hp6 x hx) h4
  rw [walk3, V_append, V_append, V_reverse, V_append, V_Ew, V_Ew] at hc
  have e := T_eq hc
  rw [T_mul, T_mul, hP] at e
  exact rel3 ht (u_sq j) e

noncomputable def piF : XT →* FG :=
  PresentedGroup.toGroup (f := fun t : Fin 6 => u t.val) (by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    rw [bval_map]
    rw [bval_congr (gen' := U) fun k => by
      rw [lift_gF]
      unfold U
      split_ifs <;> rfl]
    exact xr_val hr)

theorem piF_gX {k : ℕ} (hk : k < 6) : piF (gX k) = u k := by
  rw [show gX k = PresentedGroup.of ⟨k, hk⟩ from pgen_lt relsX hk]
  exact PresentedGroup.toGroup.of _

theorem prod_u_mem {w : List ℕ} (hw : ∀ g ∈ w, g < 6) : (w.map u).prod ∈ piF.range := by
  induction w with
  | nil => exact one_mem _
  | cons g w ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem ⟨gX g, piF_gX (hw g List.mem_cons_self)⟩
      (ih fun x hx => hw x (List.mem_cons_of_mem _ hx))

theorem hgen_mem : ∀ h ∈ CFSG.KD.FiFW.hg, V (Ew h.1) ∈ piF.range := by
  intro h hh
  have h1 := hgOK_spec hg_ok h hh
  obtain ⟨q, i, w, R⟩ := h
  unfold hgOne at h1
  obtain ⟨hi, h1⟩ := (andB_eq' _ _).1 h1
  obtain ⟨h2, h3⟩ := (andB_eq' _ _).1 h1
  obtain ⟨hw, hq⟩ := (andB_eq' _ _).1 h2
  have hw' := lt6_spec hw
  have hq' := lt6_spec hq
  have hc := walk_cen _ R (by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact lt6_pW hw' x hx
    · exact hq' x (List.mem_reverse.1 hx)) h3
  rw [V_append, V_reverse] at hc
  have e := T_eq hc
  change V (Ew q) ∈ piF.range
  rw [V_Ew, ← e, V_pW, T_mul]
  refine mul_mem (mul_mem (inv_mem (prod_u_mem hw')) ⟨gX i, piF_gX (Nat.le_of_ble_eq_true hi)⟩)
    (prod_u_mem hw')

theorem index_le : piF.range.relIndex ⊤ ≠ 0 ∧ piF.range.relIndex ⊤ ≤ 3510 := by
  have s := lceOk_sound tabH_ok gen (relsRT relsH_bind)
  have hsub : Subgroup.closure ((fun j => bval gen (wWord (sel1 CFSG.KD.FiFH.ST j))
      (wLen (sel1 CFSG.KD.FiFH.ST j))) '' {j | j < 8}) ≤ piF.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    change j < 8 at hj
    have hl8 : j < (CFSG.KD.FiFW.hg.map fun h => Ew h.1).length := by
      rw [List.length_map, lens.2.2.1]; exact hj
    have e := posBind_spec stH_bind j hl8
    rw [Nat.zero_add] at e
    have hm : (CFSG.KD.FiFW.hg.map fun h => Ew h.1).getD j [] ∈ CFSG.KD.FiFW.hg.map fun h => Ew h.1 := by
      rw [List.getD_eq_getElem _ _ hl8]
      exact List.getElem_mem hl8
    obtain ⟨h6, hlen⟩ := wordsLt_spec hWords_lt _ hm
    change bval gen (wWord (sel1 CFSG.KD.FiFH.ST j)) (wLen (sel1 CFSG.KD.FiFH.ST j)) ∈ piF.range
    rw [e, bval_posL hlen h6]
    obtain ⟨h, hh, he⟩ := List.mem_map.1 hm
    rw [← he]
    exact hgen_mem h hh
  have htop : Subgroup.closure (gen '' {g | 2 * g < 12}) = ⊤ := by
    rw [two_lt 6 12 rfl]
    exact closure_pgen relsF
  have ha : CFSG.KD.FiFH.a = 3510 := rfl
  rw [htop, ha] at s
  refine ⟨fun h0 => s.1 ?_, (Subgroup.relIndex_le_of_le_left hsub s.1).trans s.2⟩
  have := Subgroup.relIndex_dvd_of_le_left (L := ⊤) hsub
  rw [h0] at this
  exact Nat.eq_zero_of_zero_dvd this

theorem card_le : Finite FG ∧ Nat.card FG ≤ 774741019852800 := by
  obtain ⟨hfin, hcard⟩ := xt_card
  have : Finite piF.range := Finite.of_surjective _ piF.rangeRestrict_surjective
  have hr : Nat.card piF.range ≠ 0 ∧ Nat.card piF.range ≤ 12 * 18393661440 := by
    have h1 : Nat.card piF.range ≤ Nat.card XT :=
      Nat.card_le_card_of_surjective _ piF.rangeRestrict_surjective
    exact ⟨Nat.card_pos.ne', h1.trans hcard⟩
  have c := KB.card_le_step ⟨le_top, index_le.1, index_le.2⟩ hr
  rw [Subgroup.card_top] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (by norm_num)⟩

end CertificateChecks.KernelFi22F

end
