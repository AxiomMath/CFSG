module

public import Certificates.Kernel.Tits8074.Syl
public import Certificates.Kernel.Tits8074.Walk
public import Certificates.Kernel.Tits8074.GrpChk
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.Certificates.Kernel.Tits8074Aut
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT8074

open CFSG.KC.Tits8074 CFSG.Quasithin CFSG.Certificates CFSG.Monster.B.Co2 Equiv
open CFSG.KC.OrbGroup CFSG.KC.Enum CFSG.KS.Raw.Orb CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin
  Subgroup

theorem grp_facts {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {ng N : ℕ}
    {G T E D S : ℕ → ℕ} {ps : List ℕ} {g : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ k < ng, PRep n w (G k) (g k)) (hcl : ∀ i < N, closPtL n w ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn n w)
    (hps : ∀ p ∈ ps, p < n) (hK : distinctK N (fun i => pkeyK n w ps (T i)) S = true) :
    Nat.card (closure (g '' {k | k < ng})) = N ∧
      ∀ y ∈ closure (g '' {k | k < ng}), ∃ i < N, PRep n w (T i) y := by
  have h0' : PRep n w (T 0) 1 := by
    rw [h0]
    exact prep_pidn hn hw
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ := leftOrb_reps (by omega) hg hcl htr hN h0' hps hK
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) Function.injective_id g c
    ⟨0, hN, hc0⟩ hmem hcl' hinj
  refine ⟨hcard, fun y hy => ?_⟩
  obtain ⟨i, hi, e⟩ := hall y hy
  have e' : c i = y := e
  exact ⟨i, hi, e' ▸ hc i hi⟩

theorem ps_lt : ∀ p ∈ CertificateChecks.KernelT8074E.ps, p < 1755 := by decide

theorem tT0 : Nat.beq (TG.T 0) (pidn 1755 11) = true := by quickRfl

theorem hT0 : Nat.beq (HG.T 0) (pidn 1755 11) = true := by quickRfl

theorem tng : TG.ng = tg.length := by decide

theorem hng : HG.ng = 2 ∧ hw.length = 2 := by decide

theorem cw_len : cw.length = 27 := by decide

theorem prep_words {W : List (List Nat)} {G : Nat → Nat} (hW : ∀ u ∈ W, ∀ c ∈ u, c < 24)
    (h : genEq L G W 0 = true) {k : Nat} (hk : k < W.length) :
    PRep 1755 11 (G k) (wv gl (W.getD k [])) := by
  intro x
  have e := genEq_spec h k hk x x.2
  rw [zero_add] at e
  rw [List.getD_eq_getElem _ _ hk, ← ev_fin (hW _ (List.getElem_mem hk)) x]
  exact e

theorem one_of_pidn {P : Nat} {y : Perm (Fin 1755)} (hP : PRep 1755 11 P y)
    (h : Nat.beq P (pidn 1755 11) = true) : y = 1 := by
  rw [Nat.eq_of_beq_eq_true h] at hP
  exact Equiv.ext fun q => Fin.ext ((hP q).symm.trans (prep_pidn (by norm_num) (by norm_num) q))

theorem words_le {W : List (List Nat)} (hW : ∀ u ∈ W, ∀ c ∈ u, c < 24) (ng : Nat) :
    closure ((fun k => wv gl (W.getD k [])) '' {k | k < ng}) ≤ P := by
  refine (closure_le _).2 ?_
  rintro _ ⟨k, -, rfl⟩
  refine wv_mem fun c hc => ?_
  rcases Nat.lt_or_ge k W.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk] at hc
    exact hW _ (List.getElem_mem hk) c hc
  · rw [List.getD_eq_default _ _ hk] at hc
    exact absurd hc List.not_mem_nil

@[expose] noncomputable def T : Subgroup (Perm (Fin 1755)) :=
  closure ((fun k => wv gl (tg.getD k [])) '' {k | k < TG.ng})

@[expose] noncomputable def H : Subgroup (Perm (Fin 1755)) :=
  closure ((fun k => wv gl (hw.getD k [])) '' {k | k < HG.ng})

theorem T_facts : Nat.card T = 27 ∧ ∀ y ∈ T, ∃ i < 27, PRep 1755 11 (TG.T i) y := by
  have h := grp_facts (n := 1755) (w := 11) (by norm_num) (by norm_num)
    (fun k hk => prep_words ws_facts.2.2.2.2.2.2.2.1 tEq (by rwa [tng] at hk))
    TG.cl TG.tr (by norm_num) (Nat.eq_of_beq_eq_true tT0) ps_lt TG.k
  simp only [Nat.mul_one] at h
  exact h

theorem H_card : Nat.card H = 108 := by
  have h := grp_facts (n := 1755) (w := 11) (by norm_num) (by norm_num)
    (fun k hk => prep_words ws_facts.2.2.2.2.2.2.1 hEq (by rw [hng.2, ← hng.1]; exact hk))
    HG.cl HG.tr (by norm_num) (Nat.eq_of_beq_eq_true hT0) ps_lt HG.k
  simp only [Nat.mul_one] at h
  exact h.1

theorem T_le : T ≤ P := words_le ws_facts.2.2.2.2.2.2.2.1 _

theorem H_le : H ≤ P := words_le ws_facts.2.2.2.2.2.2.1 _

theorem T_conj {x : Perm (Fin 1755)} (hx : x ∈ T) : x = 1 ∨ ∃ g ∈ P, g * gl 2 * g⁻¹ = x := by
  obtain ⟨i, hi, hp⟩ := T_facts.2 x hx
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact Or.inl (one_of_pidn hp tT0)
  · right
    have hcw : i < cw.length := by rw [cw_len]; exact hi
    have hu := ws_facts.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hcw)
    have h := conjK_spec tConj i hcw (by omega)
    rw [zero_add] at h
    have hxP := T_le hx
    have hg : wv gl cw[i] * x = gl 2 * wv gl cw[i] := by
      refine eq_of_base (P.mul_mem (wv_mem hu) hxP) (P.mul_mem (gl_mem (by norm_num)) (wv_mem hu))
        fun q hq => Fin.ext ?_
      rw [Perm.mul_apply, Perm.mul_apply, ← ev_fin hu, ← ap_fin (by norm_num), ← ev_fin hu,
        ← hp q]
      exact h q hq
    refine ⟨(wv gl cw[i])⁻¹, P.inv_mem (wv_mem hu), ?_⟩
    rw [inv_inv, mul_assoc, ← hg]
    group

theorem H_comm {x : Perm (Fin 1755)} (hx : x ∈ H) : x * gl 2 = gl 2 * x := by
  have hle : H ≤ centralizer {gl 2} := by
    refine (closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk2 : k < 2 := hng.1 ▸ hk
    have hkw : k < hw.length := by rw [hng.2]; exact hk2
    have hu : ∀ c ∈ hw.getD k [], c < 24 := by
      rw [List.getD_eq_getElem _ _ hkw]
      exact ws_facts.2.2.2.2.2.2.1 _ (List.getElem_mem hkw)
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact comm_of_base (wv_mem hu) (gl_mem (by norm_num))
      (prep_words ws_facts.2.2.2.2.2.2.1 hEq hkw) (ap_fin (by norm_num))
      (commG_spec hComm k hk2)
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem walk_append {z : Nat} : ∀ (A B : List (List Nat × Nat)) (q : Nat),
    walk L z (A ++ B) q = true ↔ walk L z A q = true ∧ walk L z B (q + A.length) = true
  | [], B, q => by
    have e : walk L z [] q = true := rfl
    simp [e]
  | e :: A, B, q => by
    rw [List.cons_append]
    change bAnd(_, bAnd(_, walk L z (A ++ B) (Nat.succ q))) = true ↔
      bAnd(_, bAnd(_, walk L z A (Nat.succ q))) = true ∧ _
    rw [band_true, band_true, band_true, band_true, walk_append A B, List.length_cons,
      show Nat.succ q + A.length = q + (A.length + 1) by omega]
    tauto

theorem walk_slice {z : Nat} {A B : List (List Nat × Nat)} {q n : Nat} (hA : walk L z A q = true)
    (hl : q + A.length = n) (hB : walk L z B n = true) : walk L z (A ++ B) q = true :=
  (walk_append A B q).2 ⟨hA, hl ▸ hB⟩

theorem nGood_append (A B : List (List Nat × Nat)) : nGood (A ++ B) = nGood A + nGood B := by
  rw [nGood_eq, nGood_eq, nGood_eq, List.filter_append, List.length_append]

theorem allL_append {α : Type} {f : α → Bool} (A B : List α) :
    allL (A ++ B) f = true ↔ allL A f = true ∧ allL B f = true := by
  rw [allL_iff, allL_iff, allL_iff]
  simp only [List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact h1 a ha
    · exact h2 a ha

@[expose] noncomputable def E : List (List Nat × Nat) :=
  x0 ++ (x1 ++ (x2 ++ (x3 ++ (x4 ++ (x5 ++ (x6 ++ (x7 ++ (x8 ++ (x9 ++ (x10 ++ (x11 ++
    (x12 ++ (x13 ++ (x14 ++ x15))))))))))))))

theorem hE : walk L zc E 0 = true :=
  walk_slice w0 rfl (walk_slice w1 rfl (walk_slice w2 rfl (walk_slice w3 rfl (walk_slice w4 rfl
    (walk_slice w5 rfl (walk_slice w6 rfl (walk_slice w7 rfl (walk_slice w8 rfl
      (walk_slice w9 rfl (walk_slice w10 rfl (walk_slice w11 rfl (walk_slice w12 rfl
        (walk_slice w13 rfl (walk_slice w14 rfl w15))))))))))))))

theorem E_len : E.length = 1755 := by
  simp only [E, List.length_append]
  rfl

theorem E_good : nGood E = 216 := by
  have h := Nat.eq_of_beq_eq_true good
  simp only [E, nGood_append]
  omega

theorem E_letters : ∀ e ∈ E, ∀ c ∈ e.1, c < 24 := by
  have h := xs
  simp only [band_true] at h
  have hE' : lx E = true := by
    unfold lx at h ⊢
    simp only [E, allL_append]
    tauto
  intro e he
  exact lw_spec (allL_spec hE' e he)

theorem Y_le : {x : Perm (Fin 1755) | (∃ g ∈ P, g * gl zc * g⁻¹ = x) ∧
    (x * gl 2) ^ 13 = 1}.ncard ≤ 216 := by
  let M : List (Perm (Fin 1755)) := (E.filter fun e => e.2 == 2047).map
    fun e => wv gl e.1 * gl zc * (wv gl e.1)⁻¹
  have hsub : {x : Perm (Fin 1755) | (∃ g ∈ P, g * gl zc * g⁻¹ = x) ∧
      (x * gl 2) ^ 13 = 1} ⊆ {x | x ∈ M} := by
    rintro x ⟨⟨g, hg, rfl⟩, hx13⟩
    have hj : ((g 0 : Fin 1755) : ℕ) < E.length := by rw [E_len]; exact (g 0).2
    obtain ⟨h1, h2⟩ := walk_spec E 0 hE _ hj
    have ht := E_letters _ (List.getElem_mem hj)
    have ht0 : wv gl (E[((g 0 : Fin 1755) : ℕ)]).1 0 = g 0 := by
      apply Fin.ext
      rw [← ev_fin ht]
      simpa using h1
    have hl1 : (wv gl (E[((g 0 : Fin 1755) : ℕ)]).1)⁻¹ * g ∈ titsPairQ.levelSubgroup 1 := by
      refine (level_mem_iff (by norm_num) _).2 ⟨P.mul_mem (P.inv_mem (wv_mem ht)) hg,
        fun r hr => ?_⟩
      have e : bs.take 1 = [0] := rfl
      rw [e, List.mem_singleton] at hr
      rw [show r = 0 from Fin.ext hr, Perm.mul_apply, Perm.inv_eq_iff_eq, ht0]
    have hc := z_comm_level1 hl1
    set t := wv gl (E[((g 0 : Fin 1755) : ℕ)]).1 with ht_def
    have hx : g * gl zc * g⁻¹ = t * gl zc * t⁻¹ := by
      have e3 : g * gl zc * g⁻¹ = t * ((t⁻¹ * g) * gl zc) * (t⁻¹ * g)⁻¹ * t⁻¹ := by group
      rw [e3, ← hc]
      group
    rcases h2 with hf | ⟨hp, hne⟩
    · refine List.mem_map.2 ⟨_, List.mem_filter.2 ⟨List.getElem_mem hj, ?_⟩, hx.symm⟩
      rw [hf]
      rfl
    · exfalso
      have hi := iter_eq hL zc_lt ht 13 ⟨_, hp⟩
      have exb : xb gl zc (E[((g 0 : Fin 1755) : ℕ)]).1 = g * gl zc * g⁻¹ * gl 2 := by
        unfold xb
        rw [← ht_def, hx]
      rw [exb, hx13, Perm.one_apply] at hi
      exact hne hi
  have hfin : {x | x ∈ M}.Finite := List.finite_toSet M
  refine (Set.ncard_le_ncard hsub hfin).trans ?_
  have e : {x | x ∈ M} = (M.toFinset : Set (Perm (Fin 1755))) := by
    ext x
    simp
  rw [e, Set.ncard_coe_finset]
  refine (List.toFinset_card_le M).trans ?_
  rw [List.length_map, ← nGood_eq, E_good]

theorem b_pow : gl 2 ^ 3 = 1 := by
  rw [gl_two]
  have hp : ∀ d : Nat, Rep 1755 (powA 1755 titsB d) (titsPermB ^ d) := by
    intro d
    induction d with
    | zero =>
      rw [pow_zero]
      exact rep_idA
    | succ d ih =>
      rw [pow_succ']
      exact rep_compA rep_titsPermB ih
  exact eq_of_eqA (hp 3) rep_idA titsPair_check.2.2.2.2.2.2.2.2.2.2.2.1

theorem b_ne_one : gl 2 ≠ 1 := by
  rw [gl_two]
  intro h
  have e := (eqA_iff rep_titsPermB rep_idA).2 h
  rw [titsPair_check.2.2.2.2.2.2.2.2.2.2.2.2.1] at e
  exact Bool.false_ne_true e

theorem a_conj : ∃ g ∈ P, g * gl zc * g⁻¹ = gl 0 := by
  have haw := ws_facts.1
  refine ⟨wv gl aw, wv_mem haw, eq_of_base (P.mul_mem (P.mul_mem (wv_mem haw) (gl_mem zc_lt))
    (P.inv_mem (wv_mem haw))) (gl_mem (by norm_num)) fun q hq => Fin.ext ?_⟩
  have h := conjB_spec conj q hq
  rw [evI_eq hL aw haw, ap_fin zc_lt, ev_fin haw, ap_fin (c := 0) (by norm_num)] at h
  simp only [Perm.mul_apply]
  exact h.symm

theorem mulAut_card : Nat.card (MulAut P) ≤ 2 * 17971200 := by
  have hgen : P = closure ({gl 0, gl 2} : Set (Perm (Fin 1755))) := by
    rw [gl_zero, gl_two]
    exact titsPairQ_original'
  have hS : Nat.card Sg = 2 ^ (Nat.card P).factorization 2 := by
    rw [card_Sg, card_titsPair_chain, show (17971200 : ℕ) = 2 ^ 11 * 8775 by norm_num,
      CFSG.KC.SylowReps.pow_factorization_eq Nat.prime_two (by norm_num)]
    norm_num
  have h := mulAut_card_mul_le_of_le P (gl_mem (by norm_num)) (gl_mem (by norm_num))
    (gl_mem zc_lt) hgen Sg Sg_le hS z_mem z_ne_one (fun t ht => z_comm ht)
    (fun c hc hcc => center_Sg hc hcc) a_conj T T_le (k := 3) (m := 665600) (by rw [T_facts.1]; norm_num)
    (by rw [card_titsPair_chain]; norm_num) (by norm_num) (fun x hx => T_conj hx)
    (by rw [show 3 ^ 3 = 3 * 9 by norm_num, pow_mul, b_pow, one_pow]) b_ne_one H H_le
    (fun x hx => H_comm hx) (by rw [gl_zero, gl_two]; exact titsPermAB_pow)
  rw [H_card, card_titsPair_chain] at h
  have := h.trans (Nat.mul_le_mul_right _ Y_le)
  omega

end CertificateChecks.KernelT8074

end
