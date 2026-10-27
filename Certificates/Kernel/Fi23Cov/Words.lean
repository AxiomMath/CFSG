module

public import Certificates.Kernel.Fi23Cov.Base
public import Certificates.Kernel.Fi23R.Sound
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Kernel.Fi23M.Psi
import all Certificates.Kernel.Fi23M.Psi
import all CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Data.Kernel.Fi23Cov.Defs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23Cov

open CFSG.KC.Fi23Cov CFSG.KC.Fi23K CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th CFSG.Perm

theorem chW_nil : chW [] = true := rfl

theorem chW_cons (l : ℕ) (w : List ℕ) :
    chW (l :: w) = (Nat.blt 51 l && Nat.blt l 76 && chW w) := rfl

theorem chW_iff : ∀ w : List ℕ, chW w = true ↔ ∀ l ∈ w, 51 < l ∧ l < 76
  | [] => by simp [chW_nil]
  | l :: w => by
    rw [chW_cons, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, chW_iff w,
      List.forall_mem_cons]

theorem chA_iff : ∀ W : List (List ℕ), chA W = true ↔ ∀ w ∈ W, chW w = true
  | [] => by simp [chA]
  | w :: W => by
    change (chW w && chA W) = true ↔ _
    rw [Bool.and_eq_true, chA_iff W, List.forall_mem_cons]

theorem lenLe_iff : ∀ (W : List (List ℕ)) (n : ℕ), lenLe W n = true ↔ W.length ≤ n
  | [], n => by simp [lenLe]
  | w :: W, 0 => by simp [lenLe]
  | w :: W, n + 1 => by
    change lenLe W n = true ↔ _
    rw [lenLe_iff W n, List.length_cons]
    omega

theorem nthW_nil (i : ℕ) : nthW [] i = [] := rfl

theorem nthW_cons_zero (w : List ℕ) (l : List (List ℕ)) : nthW (w :: l) 0 = w := rfl

theorem nthW_cons_succ (w : List ℕ) (l : List (List ℕ)) (i : ℕ) :
    nthW (w :: l) (i + 1) = nthW l i := rfl

theorem nthW_mem_or : ∀ (l : List (List ℕ)) (i : ℕ), nthW l i ∈ l ∨ nthW l i = []
  | [], i => Or.inr (nthW_nil i)
  | w :: l, 0 => Or.inl (by rw [nthW_cons_zero]; exact List.mem_cons_self)
  | w :: l, i + 1 => by
    rw [nthW_cons_succ]
    rcases nthW_mem_or l i with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

theorem nthW_ge : ∀ (l : List (List ℕ)) (i : ℕ), l.length ≤ i → nthW l i = []
  | [], i, _ => nthW_nil i
  | w :: l, 0, h => absurd h (by simp)
  | w :: l, i + 1, h => by
    rw [nthW_cons_succ]
    exact nthW_ge l i (by simp at h; omega)

theorem exists_nthW : ∀ (l : List (List ℕ)) (w : List ℕ), w ∈ l → ∃ k < l.length, nthW l k = w
  | [], _, h => absurd h List.not_mem_nil
  | v :: l, w, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨k, hk, e⟩ := exists_nthW l w h
      exact ⟨k + 1, by simp; omega, by rw [nthW_cons_succ, e]⟩

theorem expC_nil (M : List (List ℕ)) : expC M [] = [] := rfl

theorem expC_cons (M : List (List ℕ)) (k : ℕ) (c : List ℕ) :
    expC M (k :: c) = nthW M k ++ expC M c := rfl

theorem catW_nil : catW [] = [] := rfl

theorem catW_cons (w : List ℕ) (R : List (List ℕ)) : catW (w :: R) = w ++ catW R := rfl

theorem repW_zero (w : List ℕ) : repW w 0 = [] := rfl

theorem repW_succ (w : List ℕ) (p : ℕ) : repW w (p + 1) = w ++ repW w p := rfl

@[expose] def okC (c : ℕ) : Prop := c < 10 ∨ c = 39 ∨ c = 40 ∨ c = 41 ∨ (52 ≤ c ∧ c < 76)

@[expose] def okW (w : List ℕ) : Prop := ∀ c ∈ w, okC c

theorem okW_nil : okW [] := fun _ h => absurd h List.not_mem_nil

theorem okW_append {u v : List ℕ} (hu : okW u) (hv : okW v) : okW (u ++ v) := fun c hc =>
  (List.mem_append.1 hc).elim (hu c) (hv c)

theorem okW_of_chW {w : List ℕ} (h : chW w = true) : okW w := fun c hc => by
  have := (chW_iff w).1 h c hc
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, this.2⟩)))

theorem okW_lit {w : List ℕ} (h : ∀ c ∈ w, c < 10 ∨ c = 39 ∨ c = 40 ∨ c = 41 ∨ (52 ≤ c ∧ c < 76)) :
    okW w := h

theorem okW_nthW {W : List (List ℕ)} (h : chA W = true) (i : ℕ) : okW (nthW W i) := by
  rcases nthW_mem_or W i with hm | hm
  · exact okW_of_chW ((chA_iff W).1 h _ hm)
  · rw [hm]
    exact okW_nil

theorem okW_expC {M : List (List ℕ)} (h : chA M = true) : ∀ c : List ℕ, okW (expC M c)
  | [] => okW_nil
  | k :: c => by
    rw [expC_cons]
    exact okW_append (okW_nthW h k) (okW_expC h c)

theorem okW_catW : ∀ {R : List (List ℕ)}, chA R = true → okW (catW R)
  | [], _ => okW_nil
  | w :: R, h => by
    change (chW w && chA R) = true at h
    rw [Bool.and_eq_true] at h
    rw [catW_cons]
    exact okW_append (okW_of_chW h.1) (okW_catW h.2)

theorem okW_repW {w : List ℕ} (h : okW w) : ∀ p : ℕ, okW (repW w p)
  | 0 => okW_nil
  | p + 1 => by
    rw [repW_succ]
    exact okW_append h (okW_repW h p)

section Elements


@[expose] noncomputable def jL (c : ℕ) : J :=
  if c < 10 then CFSG.Sporadic.Bridge.Fi23.img c else if c = 39 then a else if c = 40 then b
  else if c = 41 then b⁻¹ else pairG gs (c - 52)

@[expose] noncomputable def wJ : List ℕ → J
  | [] => 1
  | c :: w => wJ w * jL c

theorem wJ_nil : wJ [] = 1 := rfl

theorem wJ_cons (c : ℕ) (w : List ℕ) : wJ (c :: w) = wJ w * jL c := rfl

theorem wJ_append : ∀ u v : List ℕ, wJ (u ++ v) = wJ v * wJ u
  | [], v => by rw [List.nil_append, wJ_nil, mul_one]
  | c :: u, v => by rw [List.cons_append, wJ_cons, wJ_append u v, wJ_cons, mul_assoc]

theorem wJ_single (c : ℕ) : wJ [c] = jL c := by rw [wJ_cons, wJ_nil, one_mul]

theorem wJ_repW (w : List ℕ) : ∀ p : ℕ, wJ (repW w p) = wJ w ^ p
  | 0 => rfl
  | p + 1 => by rw [repW_succ, wJ_append, wJ_repW w p, pow_succ]

theorem jL_img {c : ℕ} (hc : c < 10) : jL c = CFSG.Sporadic.Bridge.Fi23.img c := by
  unfold jL
  rw [if_pos hc]

theorem jL_39 : jL 39 = a := by
  unfold jL
  simp

theorem jL_40 : jL 40 = b := by
  unfold jL
  simp

theorem jL_41 : jL 41 = b⁻¹ := by
  unfold jL
  simp

theorem jL_chain {c : ℕ} (h1 : 52 ≤ c) : jL c = pairG gs (c - 52) := by
  unfold jL
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem wJ_39 : wJ [39] = a := by rw [wJ_single, jL_39]

theorem wJ_40 : wJ [40] = b := by rw [wJ_single, jL_40]

theorem wJ_41 : wJ [41] = b⁻¹ := by rw [wJ_single, jL_41]

theorem wJ_chain : ∀ l : List ℕ,
    wJ ((l.reverse).map (52 + ·)) = (l.map (pairG gs)).prod
  | [] => rfl
  | x :: l => by
    have e : ((x :: l).reverse).map (52 + ·) = (l.reverse.map (52 + ·)) ++ [52 + x] := by simp
    rw [e, wJ_append, wJ_chain l, wJ_single, jL_chain (by omega), Nat.add_sub_cancel_left,
      List.map_cons, List.prod_cons]

theorem orb_eq : orb = CFSG.KD.Fi23K.orbLit := CFSG.KD.Fi23K.orbitData_eq'

theorem genG_one : genG 1 = a := by
  unfold genG
  simp

theorem genG_two : genG 2 = b := by
  unfold genG
  simp

theorem genG_neg_two : genG (-2) = b⁻¹ := by
  unfold genG
  simp

theorem tb_gen {z : ℤ} (hz : z = 1 ∨ z = 2 ∨ z = -2) {x : ℕ} (hx : x < 31671) :
    tb CFSG.KD.Fi23K.G (CFSG.KD.Fi23K.regZ z) x = idx 31671 (genG z) x := by
  have h1 := ((CFSG.KD.Fi23K.genTables_TR (z := z) (by omega) (by omega)).2 x hx).1
  have h2 := rep_gen z x hx
  rw [orb_eq] at h2
  rw [← h1, h2]

theorem letters_size' : letters.size = 24 := by
  change (chainLetters orb).size = 24
  rw [orb_eq]
  exact CFSG.KD.Fi23K.letters_TR.1

theorem tb_chain {l : ℕ} (hl : l < 24) {x : ℕ} (hx : x < 31671) :
    tb CFSG.KD.Fi23K.G (52 + l) x = idx 31671 (pairG gs l) x := by
  have h1 := ((CFSG.KD.Fi23K.letters_TR.2 l hl).2 x hx).1
  have h2 := rep_pairG_all l (by rw [letters_size']; exact hl) x hx
  have e : letters = chainLetters CFSG.KD.Fi23K.orbLit := by
    change chainLetters orb = _
    rw [orb_eq]
  rw [e] at h2
  rw [← h2, h1]
  rfl

noncomputable abbrev act : J →* Equiv.Perm (Fin 31671) := MulAction.toPermHom J (Fin 31671)

theorem act_eq {g : J} {p : Equiv.Perm (Fin 31671)}
    (h : ∀ x (hx : x < 31671), idx 31671 g x = (p ⟨x, hx⟩).val) : act g = p := by
  ext ⟨x, hx⟩
  rw [← h x hx, idx_of_lt g hx]
  rfl

private noncomputable def tJ : CertificateChecks.KernelFi23M.PG →* J :=
  CFSG.Sporadic.Bridge.Fi23.toJ

private theorem tJ_gen {k : ℕ} (hk : k < 10) :
    tJ (CertificateChecks.KernelFi23M.gen k) = CFSG.Sporadic.Bridge.Fi23.img k := by
  have hk' : k < TauCeti.Sporadic.fi23Presentation.generatorCount := by
    rw [CFSG.Sporadic.Bridge.Fi23.generatorCount_eq]
    exact hk
  change CFSG.Sporadic.Bridge.presHom TauCeti.Sporadic.fi23Presentation
    CFSG.Sporadic.Bridge.Fi23.img CFSG.Sporadic.Bridge.Fi23.relators_eval
    (CFSG.Sporadic.Bridge.presGen TauCeti.Sporadic.fi23Presentation k) = _
  exact CFSG.Sporadic.Bridge.presHom_presGen _ _ _ hk'

private theorem tJ_surjective : Function.Surjective tJ := CFSG.Sporadic.Bridge.Fi23.toJ_surjective

private theorem tJ_injective : Function.Injective tJ := by
  have hfin := CFSG.Sporadic.Presentation.Fi23.finite_card_le
  have : Finite CertificateChecks.KernelFi23M.PG := hfin.1
  refine (tJ_surjective.bijective_of_nat_card_le ?_).1
  rw [card_J]
  exact hfin.2

private theorem of_eq_gen (i : Fin CFSG.KD.Fi23K.P23.generatorCount) :
    PresentedGroup.of i = CertificateChecks.KernelFi23M.gen i.val := by
  unfold CertificateChecks.KernelFi23M.gen
  rw [dif_pos i.isLt]

private theorem subtype_tJ : J.subtype.comp tJ = CertificateChecks.KernelFi23M.σ := by
  refine PresentedGroup.ext fun i => ?_
  have hi : i.val < 10 := lt_of_lt_of_eq i.isLt CFSG.KD.Fi23K.generatorCount_P23
  rw [of_eq_gen, MonoidHom.comp_apply, tJ_gen hi, CertificateChecks.KernelFi23M.σ_gen hi]
  apply Units.ext
  rw [CertificateChecks.KernelFi23M.u_val hi]
  obtain ⟨hX, -⟩ :=
    Classical.choose_spec (Certificates.certificate9206).2.2.2
  exact CFSG.Sporadic.Bridge.Fi23.mat_img hX hi

private theorem mat_tJ (g : CertificateChecks.KernelFi23M.PG) :
    mat (tJ g) = (CertificateChecks.KernelFi23M.σ g).val := by
  rw [← subtype_tJ]
  rfl

private theorem tJ_wα : tJ CertificateChecks.KernelFi23M.wα = a := by
  apply mat_injective
  rw [mat_tJ, CertificateChecks.KernelFi23M.σ_wα, mat_a]

private theorem tJ_wβ : tJ CertificateChecks.KernelFi23M.wβ = b := by
  apply mat_injective
  rw [mat_tJ, CertificateChecks.KernelFi23M.σ_wβ, mat_b]

private theorem closure_w :
    Subgroup.closure ({CertificateChecks.KernelFi23M.wα, CertificateChecks.KernelFi23M.wβ} :
      Set CertificateChecks.KernelFi23M.PG) = ⊤ := by
  apply Subgroup.map_injective tJ_injective
  rw [MonoidHom.map_closure, Set.image_pair, tJ_wα, tJ_wβ, closure_ab, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 tJ_surjective]

theorem act_a : act a = CFSG.KD.Fi23K.phiX CertificateChecks.KernelFi23M.wα :=
  act_eq fun x hx => by
    rw [CertificateChecks.KernelFi23M.phiX_wα x hx, ← genG_one, ← tb_gen (Or.inl rfl) hx]
    rfl

theorem act_b : act b = CFSG.KD.Fi23K.phiX CertificateChecks.KernelFi23M.wβ :=
  act_eq fun x hx => by
    rw [CertificateChecks.KernelFi23M.phiX_wβ x hx, ← genG_two, ← tb_gen (Or.inr (Or.inl rfl)) hx]
    rfl

private theorem act_tJ : act.comp tJ = CFSG.KD.Fi23K.phiX := by
  refine MonoidHom.eq_of_eqOn_dense closure_w ?_
  rintro w (rfl | rfl)
  · rw [MonoidHom.comp_apply, tJ_wα, act_a]
  · rw [MonoidHom.comp_apply, tJ_wβ, act_b]

theorem tb_img {k : ℕ} (hk : k < 10) {x : ℕ} (hx : x < 31671) :
    tb CFSG.KD.Fi23K.G k x = idx 31671 (CFSG.Sporadic.Bridge.Fi23.img k) x := by
  have h : act (CFSG.Sporadic.Bridge.Fi23.img k) = CFSG.KD.Fi23K.xS k := by
    rw [← tJ_gen hk, ← MonoidHom.comp_apply, act_tJ, CertificateChecks.KernelFi23M.phiX_gen hk]
  rw [← CFSG.KD.Fi23K.xS_acts hk x hx, ← h, idx_of_lt _ hx]
  rfl

theorem tb_jL {c : ℕ} (hc : okC c) {x : ℕ} (hx : x < 31671) :
    tb CFSG.KD.Fi23K.G c x = idx 31671 (jL c) x := by
  rcases hc with h | rfl | rfl | rfl | ⟨h1, h2⟩
  · rw [jL_img h]
    exact tb_img h hx
  · rw [jL_39, ← genG_one]
    exact tb_gen (Or.inl rfl) hx
  · rw [jL_40, ← genG_two]
    exact tb_gen (Or.inr (Or.inl rfl)) hx
  · rw [jL_41, ← genG_neg_two]
    exact tb_gen (Or.inr (Or.inr rfl)) hx
  · rw [jL_chain h1]
    have := tb_chain (l := c - 52) (by omega) hx
    have e : 52 + (c - 52) = c := by omega
    rwa [e] at this

theorem wa_wJ : ∀ w : List ℕ, okW w → ∀ x < 31671,
    CFSG.KC.Fi23R.wa CFSG.KD.Fi23K.G w x = idx 31671 (wJ w) x
  | [], _, x, _ => by rw [CertificateChecks.KernelFi23R.wa_nil, wJ_nil, idx_one]
  | c :: w, h, x, hx => by
    have hc := h c List.mem_cons_self
    have hw : okW w := fun d hd => h d (List.mem_cons_of_mem c hd)
    have hc128 : c < 128 := by
      unfold okC at hc
      omega
    rw [CertificateChecks.KernelFi23R.wa_cons, CertificateChecks.KernelFi23R.lf_eq, if_pos hc128,
      tb_jL hc hx, wa_wJ w hw _ (idx_lt _ hx), wJ_cons, idx_mul]

theorem eqw {u v : List ℕ} (hu : okW u) (hv : okW v) (h : E u v = true) : wJ u = wJ v := by
  have h1 : (wJ v)⁻¹ * wJ u = 1 := by
    apply sep
    intro t ht
    have hs : chainQ.size = 6 := rfl
    rw [hs] at ht
    have e : chainQ[t]! = t := by
      interval_cases t <;> rfl
    rw [e]
    have hb := CertificateChecks.KernelFi23R.eqB_spec h t ht
    have ht' : t < 31671 := lt_trans ht (by norm_num)
    rw [wa_wJ u hu t ht', wa_wJ v hv t ht'] at hb
    rw [idx_mul, hb, ← idx_mul, inv_mul_cancel, idx_one]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem E_of_eq {u v : List ℕ} (hu : okW u) (hv : okW v) (h : wJ u = wJ v) : E u v = true := by
  change CFSG.KC.Fi23R.eqB CFSG.KD.Fi23K.G u v = true
  unfold CFSG.KC.Fi23R.eqB
  refine CFSG.KS.Raw.Orb.allN_iff.2 fun b hb => ?_
  have hb' : b < 31671 := lt_trans hb (by norm_num)
  rw [Nat.beq_eq, wa_wJ u hu b hb', wa_wJ v hv b hb', h]

theorem comm_of {u v : List ℕ} (hu : okW u) (hv : okW v) (h : cm E u v = true) :
    wJ u * wJ v = wJ v * wJ u := by
  have e := eqw (okW_append hu hv) (okW_append hv hu) h
  rw [wJ_append, wJ_append] at e
  exact e.symm

theorem wJ_mem_expC {L : Subgroup J} {M : List (List ℕ)} (h : ∀ k, wJ (nthW M k) ∈ L) :
    ∀ c, wJ (expC M c) ∈ L
  | [] => by
    rw [expC_nil, wJ_nil]
    exact L.one_mem
  | k :: c => by
    rw [expC_cons, wJ_append]
    exact L.mul_mem (wJ_mem_expC h c) (h k)

theorem wJ_mem_catW {L : Subgroup J} : ∀ {R : List (List ℕ)}, (∀ w ∈ R, wJ w ∈ L) →
    wJ (catW R) ∈ L
  | [], _ => by
    rw [catW_nil, wJ_nil]
    exact L.one_mem
  | w :: R, h => by
    rw [catW_cons, wJ_append]
    exact L.mul_mem (wJ_mem_catW fun v hv => h v (List.mem_cons_of_mem _ hv))
      (h w List.mem_cons_self)

theorem wJ_mem_of_nthW {L : Subgroup J} {R : List (List ℕ)} {n : ℕ} (hn : R.length ≤ n)
    (h : ∀ k < n, wJ (nthW R k) ∈ L) : ∀ k, wJ (nthW R k) ∈ L := by
  intro k
  by_cases hk : k < n
  · exact h k hk
  · rw [nthW_ge R k (by omega), wJ_nil]
    exact L.one_mem

theorem wJ_mem_catW' {L : Subgroup J} {R : List (List ℕ)} (h : ∀ k, wJ (nthW R k) ∈ L) :
    wJ (catW R) ∈ L :=
  wJ_mem_catW fun w hw => by
    obtain ⟨k, -, rfl⟩ := exists_nthW R w hw
    exact h k

end Elements

end CFSG.KD.Fi23Cov

end
