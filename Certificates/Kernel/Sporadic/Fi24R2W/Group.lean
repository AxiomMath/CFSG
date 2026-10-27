
module

public import Certificates.Kernel.Sporadic.Fi24R2W.Checks
public import Certificates.Kernel.Sporadic.Fi24R2W.Planes
public import Certificates.Kernel.Sporadic.Fi24OrbL.Cls
public import Certificates.Kernel.Sporadic.Fi24K.C2077
public import CFSG.Certificates.Kernel.HeFixKFix

public section

set_option maxRecDepth 4000

namespace CertificateChecks.KernelSpor.Fi24R2W

open CFSG.KC.Fi24R2W CFSG.KD.Fi24Net CFSG.KC.Enum CFSG.KS.Fi24Kit CFSG.KS.Fi24Net
  CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native
  CFSG.Sporadic.Th CFSG.Perm CertificateChecks.KernelFi24OrbL CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem walkN_cons (l : Nat) (t : List Nat) (x : Nat) :
    walkN NW (l :: t) x = walkN NW t (CFSG.KC.Fi24NetPt.letN NW l x) :=
  CFSG.KS.Fi24NetPt.strictN_eq _ _

theorem walkN_eq : ∀ (w : List Nat) (x : Nat), walkN NW w x = wN NW w.reverse x
  | [], _ => rfl
  | l :: t, x => by
    rw [walkN_cons, walkN_eq t, List.reverse_cons, wN_append, CFSG.KS.Fi24NetPt.letN_eq]
    rfl

theorem wv {c : List Nat} (hc : ∀ l ∈ c, l < 26) : WV NW c := fun l hl =>
  (net_spec (nck_spec (l / 2) (by have := hc l hl; omega))).1

section Prod

@[expose] noncomputable def prodC (cs : List Nat) : J := (cs.map (pairG gs)).prod

theorem idx_prodC : ∀ (cs : List Nat), (∀ l ∈ cs, l < 26) → ∀ p < 306936,
    idx 306936 (prodC cs) p = wN NW cs p ∧ wN NW cs p < 306936
  | [], _, p, hp => ⟨by rw [prodC, List.map_nil, List.prod_nil, idx_one]; rfl, hp⟩
  | l :: cs, h, p, hp => by
    obtain ⟨ih1, ih2⟩ := idx_prodC cs (fun l' hl' => h l' (List.mem_cons_of_mem l hl')) p hp
    have hl := h l List.mem_cons_self
    have e : wN NW (l :: cs) p = LN NW l (wN NW cs p) := rfl
    have e2 : prodC (l :: cs) = pairG gs l * prodC cs := by
      rw [prodC, List.map_cons, List.prod_cons]
      rfl
    rw [e, e2, idx_mul, ih1, pairG_LN l hl _ ih2]
    exact ⟨rfl, LN_lt_N hl ih2⟩

theorem prodC_append (a b : List Nat) : prodC (a ++ b) = prodC a * prodC b := by
  rw [prodC, List.map_append, List.prod_append]
  rfl

theorem prodC_rep (c : List Nat) : ∀ n, prodC (List.replicate n c).flatten = prodC c ^ n
  | 0 => by rw [List.replicate_zero, List.flatten_nil, pow_zero]; rfl
  | n + 1 => by rw [List.replicate_succ, List.flatten_cons, prodC_append, prodC_rep c n, pow_succ']

theorem xor_one_eq {l : Nat} : Nat.xor l 1 = CFSG.Perm.Native.invL l := by
  unfold CFSG.Perm.Native.invL
  split_ifs with h
  · obtain ⟨j, rfl⟩ : ∃ j, l = 2 * j := ⟨l / 2, by omega⟩
    rw [show 2 * j + 1 = (2 * j) ^^^ 1 from (xor_one_even j).symm]
    rfl
  · obtain ⟨j, rfl⟩ : ∃ j, l = 2 * j + 1 := ⟨l / 2, by omega⟩
    rw [show 2 * j + 1 - 1 = (2 * j + 1) ^^^ 1 by rw [xor_one_odd j]; omega]
    rfl

theorem prodC_invC (cs : List Nat) : prodC (invC cs) = (prodC cs)⁻¹ := by
  rw [prodC, prodC, invC, List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  apply List.map_congr_left
  intro l _
  change pairG gs (Nat.xor l 1) = (pairG gs l)⁻¹
  rw [xor_one_eq, pairG_invL]

theorem prodC_hwS (A B : List Nat) : ∀ w : List Nat,
    prodC (hwS A B w) = (w.map fun x => if x = 0 then prodC A else prodC B).prod
  | [] => rfl
  | x :: w => by
    have e : hwS A B (x :: w) = (if x = 0 then A else B) ++ hwS A B w := by
      simp [hwS]
    rw [e, prodC_append, prodC_hwS A B w, List.map_cons, List.prod_cons]
    split_ifs <;> rfl

theorem base_lt : ∀ b ∈ base, b < 306936 := by decide

theorem eq_of_stage {X Y : List Nat} (hX : ∀ l ∈ X, l < 26) (hY : ∀ l ∈ Y, l < 26)
    (h : stageOK NW X Y = true) : prodC X = prodC Y := by
  have hv : ∀ b ∈ base, idx 306936 (prodC X) b = idx 306936 (prodC Y) b := by
    intro b hb
    have e := Nat.eq_of_beq_eq_true (List.all_eq_true.1 h b hb)
    rw [walkN_eq, walkN_eq, List.reverse_reverse, List.reverse_reverse] at e
    rw [(idx_prodC X hX b (base_lt b hb)).1, (idx_prodC Y hY b (base_lt b hb)).1, e]
  have hs := sep ((prodC Y)⁻¹ * prodC X) fun t ht => by
    rw [chainBase_size] at ht
    have hm : chainBase[t]! ∈ base := by
      rw [bp_eq ht]
      interval_cases t <;> decide +kernel
    rw [idx_mul, hv _ hm, idx_inv_idx]
  rw [inv_mul_eq_one] at hs
  exact hs.symm

theorem extWord_prodC {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0) : extWord w = prodC (w.map conv) := by
  unfold extWord wordG prodC
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun z hz => genLetterG_eq (hw z hz)

end Prod

theorem fpts_get {j : Nat} (hj : j < 504) : fi24FPts[j]! = fpt FP.F j := by
  rw [fp_eq, CFSG.KC.HeFixK.unpack_getElem! hj]
  rfl

theorem kstrong_get' {r j : Nat} (hr : r < 2) (hj : j < 504) :
    (fi24KStrong[r]!)[j]! = krow (Fi24KC.S r) j := by
  rw [CertificateChecks.KernelSpor.Fi24C.kS, CertificateChecks.KernelSpor.Fi24C.ofFn_get (by omega),
    CFSG.KC.HeFixK.unpack_getElem! hj]
  rfl

theorem fpt_mono {i j : Nat} (hij : i < j) (hj : j < 504) : fpt FP.F i < fpt FP.F j := by
  have hm := CFSG.KS.allN_spec mono_t
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := Nat.le_of_ble_eq_true (hm j (by omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact (ih h (by omega)).trans h1
    · subst h
      exact h1

theorem fpt_lt {j : Nat} (hj : j < 504) : fpt FP.F j < 306936 := by
  have ht := Nat.le_of_ble_eq_true top_t
  rcases Nat.lt_or_ge j 503 with h | h
  · exact (fpt_mono h (by norm_num)).trans ht
  · rw [show j = 503 by omega]
    exact ht

theorem fpt_inj {i j : Nat} (hi : i < 504) (hj : j < 504) (h : fpt FP.F i = fpt FP.F j) : i = j := by
  rcases lt_trichotomy i j with hl | he | hg
  · exact absurd h (fpt_mono hl hj).ne
  · exact he
  · exact absurd h (fpt_mono hg hi).ne'

theorem fpts_facts : FPtsFacts := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [fpts_get (by omega), fpts_get (by omega)]
    exact fpt_mono (by omega) (by omega)
  · rw [fpts_get (by norm_num)]
    exact fpt_lt (by norm_num)

theorem mem_selP {f : Nat → Nat} {b x : Nat} :
    x ∈ selP FP.F f b ↔ ∃ i < 504, (b = 9 ∨ (f i).testBit b = true) ∧ fpt FP.F i = x := by
  unfold selP
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_filter, List.mem_range, Bool.or_eq_true] at hi
    exact ⟨i, hi.1, hi.2.imp (fun h => Nat.eq_of_beq_eq_true h) id, rfl⟩
  · rintro ⟨i, hi, hb, rfl⟩
    refine ⟨i, ?_, rfl⟩
    rw [List.mem_filter, List.mem_range, Bool.or_eq_true]
    exact ⟨hi, hb.imp (fun h => by rw [h]; exact Nat.beq_refl 9) id⟩

theorem plane_act {c : List Nat} (hc : ∀ l ∈ c, l < 26) {f : Nat → Nat}
    (hf : ∀ j < 504, f j < 504) (h : plOK NW c FP.F f = true) :
    ∀ j < 504, wN NW c (fpt FP.F j) = fpt FP.F (f j) := by
  have hb : ∀ b < 10, CFSG.KC.Fi24Kit.walkP NW c (CFSG.KC.Fi24ThreeO.plOf (selP FP.F (fun i => i) b)) = CFSG.KC.Fi24ThreeO.plOf (selP FP.F f b) :=
    fun b hb => Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h b hb)
  have key : ∀ b < 10, ∀ q, q ∈ selP FP.F f b ↔ wN NW c q ∈ selP FP.F (fun i => i) b := by
    intro b hb' q
    rw [← CFSG.KS.Fi24ThreeO.testBit_plOf, ← hb b hb', testBit_walkP c (wv hc), CFSG.KS.Fi24ThreeO.testBit_plOf]
  intro j hj
  set q := fpt FP.F j
  have hq9 : q ∈ selP FP.F f 9 := mem_selP.2 ⟨j, hj, Or.inl rfl, rfl⟩
  obtain ⟨i, hi, -, hiq⟩ := mem_selP.1 ((key 9 (by norm_num) q).1 hq9)
  rw [← hiq]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb9 : b < 9
  · have e1 : i.testBit b = true ↔ (f j).testBit b = true := by
      constructor
      · intro hib
        have hm : wN NW c q ∈ selP FP.F (fun i => i) b := by
          rw [← hiq]
          exact mem_selP.2 ⟨i, hi, Or.inr hib, rfl⟩
        obtain ⟨j', hj', hb', e⟩ := mem_selP.1 ((key b (by omega) q).2 hm)
        rw [fpt_inj hj' hj e] at hb'
        exact hb'.resolve_left (by omega)
      · intro hjb
        obtain ⟨i', hi', hb', e⟩ := mem_selP.1 ((key b (by omega) q).1
          (mem_selP.2 ⟨j, hj, Or.inr hjb, rfl⟩))
        rw [← hiq] at e
        rw [fpt_inj hi' hi e] at hb'
        exact hb'.resolve_left (by omega)
    cases h1 : i.testBit b <;> cases h2 : (f j).testBit b <;> simp_all
  · have hp : 512 ≤ 2 ^ b := by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by have := hf j hj; omega)]

section Group

@[expose] noncomputable def phi : CFSG.Sporadic.Fi23.J →* J :=
  M.subtype.comp (@MulEquiv.toMonoidHom CFSG.Sporadic.Fi23.J M inferInstance inferInstance
    fi23EquivM.symm)

theorem phi_apply (u : CFSG.Sporadic.Fi23.J) : phi u = (fi23EquivM.symm u : J) := rfl

theorem H0_eq : localWords[0]!.map conv = H0 := by decide +kernel

theorem H1_eq : localWords[1]!.map conv = H1 := by decide +kernel

theorem localWords_ne {i : Nat} (hi : i < 2) : ∀ z ∈ localWords[i]!, z ≠ 0 := fun z hz => by
  have := (localWords_letters hi z hz).1
  omega

theorem phi_a : phi CFSG.Sporadic.Fi23.a = prodC S0 := by
  rw [phi_apply, ← fi23EquivM_mGen0, MulEquiv.symm_apply_apply]
  change extWord localWords[0]! = _
  rw [extWord_prodC (localWords_ne (by norm_num)), H0_eq]
  exact eq_of_stage (by decide +kernel) (by decide +kernel) st0_t

theorem phi_b : phi CFSG.Sporadic.Fi23.b = prodC S1 := by
  rw [phi_apply, ← fi23EquivM_mGen1, MulEquiv.symm_apply_apply]
  change extWord localWords[1]! = _
  rw [extWord_prodC (localWords_ne (by norm_num)), H1_eq]
  exact eq_of_stage (by decide +kernel) (by decide +kernel) st1_t

theorem phi_wordJ (w : List Nat) : phi (CFSG.Sporadic.Fi23.wordJ w) = prodC (hwS S0 S1 w) := by
  rw [prodC_hwS, CFSG.Sporadic.Fi23.wordJ, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  by_cases hx : x = 0
  · simp [hx, phi_a]
  · simp [hx, phi_b]

theorem phi_d : phi CFSG.Sporadic.Fi23.d = prodC SD := by
  rw [show CFSG.Sporadic.Fi23.d = CFSG.Sporadic.Fi23.wordJ dWL ^ 7 from rfl, map_pow, phi_wordJ,
    eq_of_stage (by decide +kernel) (by decide +kernel) st2_t, ← prodC_rep]
  exact eq_of_stage (by decide +kernel) (by decide +kernel) st3_t

theorem phi_u2 : phi fi23U2 = prodC SU2 := by
  have ha : CFSG.Sporadic.Fi23.genG 1 = CFSG.Sporadic.Fi23.a := by simp [CFSG.Sporadic.Fi23.genG]
  have hai : CFSG.Sporadic.Fi23.genG (-1) = CFSG.Sporadic.Fi23.a⁻¹ := by
    simp [CFSG.Sporadic.Fi23.genG]
  rw [fi23U2, ha, hai, map_mul, map_mul, map_mul, map_inv, phi_d, phi_a, ← prodC_invC,
    ← prodC_append, ← prodC_append, ← prodC_append]
  exact eq_of_stage (by decide +kernel) (by decide +kernel) st4_t

theorem wordW_eq : wordG CFSG.Sporadic.Fi23.genG fi23WordW = CFSG.Sporadic.Fi23.wordJ wWL := by
  simp [wordG, CFSG.Sporadic.Fi23.wordJ, fi23WordW, wWL, CFSG.Sporadic.Fi23.genG]

theorem phi_w : phi (wordG CFSG.Sporadic.Fi23.genG fi23WordW) = prodC SW := by
  rw [wordW_eq, phi_wordJ]
  exact eq_of_stage (by decide +kernel) (by decide +kernel) st5_t

theorem fi24R2_eq : fi24R2 = prodC SR := by
  change phi fi23U3 = _
  rw [fi23U3, map_mul, map_mul, map_mul, map_inv, phi_u2, phi_w, phi_d, ← prodC_invC,
    ← prodC_append, ← prodC_append, ← prodC_append]
  exact eq_of_stage (by decide +kernel) (by decide +kernel) st6_t

theorem bray_eq (g : List ℤ) (G : List Nat) (hg : ∀ z ∈ g, z ≠ 0) (hG : g.map conv = G) (e : Nat) :
    brayElt fi24R2 (wordG genLetterG g) e = prodC (bray G e) := by
  change brayElt fi24R2 (extWord g) e = _
  rw [extWord_prodC hg, hG, fi24R2_eq, brayElt, bray, prodC_append, prodC_rep, prodC_append,
    prodC_append, prodC_append, prodC_invC]

theorem fi24Ca_eq : fi24Ca = prodC SA :=
  (bray_eq _ _ (by decide) (by decide) _).trans (eq_of_stage (by decide +kernel) (by decide +kernel) stA_t)

theorem fi24Cb_eq : fi24Cb = prodC SB :=
  (bray_eq _ _ (by decide) (by decide) _).trans (eq_of_stage (by decide +kernel) (by decide +kernel) stB_t)

theorem comm_of {c : List Nat} (hc : ∀ l ∈ c, l < 26) (h : stageOK NW (c ++ SR) (SR ++ c) = true) :
    prodC c * fi24R2 = fi24R2 * prodC c := by
  have hS : ∀ l ∈ SR, l < 26 := by decide
  rw [fi24R2_eq, ← prodC_append, ← prodC_append]
  exact eq_of_stage (List.forall_mem_append.2 ⟨hc, hS⟩) (List.forall_mem_append.2 ⟨hS, hc⟩) h

theorem act_of {c : List Nat} (hc : ∀ l ∈ c, l < 26) {r : Nat} (hr : r < 2)
    (hK : ∀ j < 504, krow (Fi24KC.S r) j < 504) (h : plOK NW c FP.F (krow (Fi24KC.S r)) = true) :
    ∀ j < 504, idx 306936 (prodC c) fi24FPts[j]! = fi24FPts[(fi24KStrong[r]!)[j]!]! := by
  intro j hj
  rw [kstrong_get' hr hj, fpts_get hj, fpts_get (hK j hj), (idx_prodC c hc _ (fpt_lt hj)).1]
  exact plane_act hc hK h j hj

theorem fix_SR : ∀ j < 504, idx 306936 fi24R2 (fpt FP.F j) = fpt FP.F j := by
  intro j hj
  rw [fi24R2_eq, (idx_prodC SR (by decide) _ (fpt_lt hj)).1]
  exact plane_act (f := fun i => i) (by decide) (fun j hj => hj) fix_t j hj

attribute [local instance] CFSG.Sporadic.Fi24.rAction in
theorem card_fix : Nat.card {k : Fin 306936 // fi24R2 • k = k} = 504 := by
  have h := (KernelFi24G2g.wit2078_facts pt_sp_rank).1 2 (by norm_num)
  change Nat.card {x : D24 // rep7 2 * x * (rep7 2)⁻¹ = x} = 504 at h
  rw [card_fixed_D24_pts] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun k => by
    rw [show rep7 2 = jR fi24R2 from rfl, jR_smul])

theorem fix_iff (k : Fin 306936) : fi24R2 • k = k ↔ ∃ j < 504, fi24FPts[j]! = k.val := by
  classical
  let g : Nat → Fin 306936 := fun j => if h : j < 504 then ⟨fpt FP.F j, fpt_lt h⟩ else 0
  have hfix : ∀ j < 504, fi24R2 • g j = g j := by
    intro j hj
    apply Fin.ext
    simp only [g, dif_pos hj]
    rw [← idx_of_lt fi24R2 (fpt_lt hj)]
    exact fix_SR j hj
  let S := Finset.univ.filter fun k : Fin 306936 => fi24R2 • k = k
  have hS : S.card = 504 := by
    rw [← card_fix, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hT : (Finset.range 504).image g = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hfix j (Finset.mem_range.1 hj)⟩
    · rw [hS, Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj e
      have hi' := Finset.mem_range.1 hi
      have hj' := Finset.mem_range.1 hj
      have e' := congrArg Fin.val e
      simp only [g, dif_pos hi', dif_pos hj'] at e'
      exact fpt_inj hi' hj' e'
  constructor
  · intro hk
    have : k ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
    rw [← hT] at this
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 this
    have hj' := Finset.mem_range.1 hj
    refine ⟨j, hj', ?_⟩
    simp only [g, dif_pos hj']
    exact fpts_get hj'
  · rintro ⟨j, hj, e⟩
    have hk : k = g j := by
      apply Fin.ext
      simp only [g, dif_pos hj]
      rw [← e, fpts_get hj]
    rw [hk]
    exact hfix j hj

theorem r2_facts : R2Facts := by
  have kr0 := fun j hj => Nat.le_of_ble_eq_true (CFSG.KS.allN_spec kr0_t j hj)
  have kr1 := fun j hj => Nat.le_of_ble_eq_true (CFSG.KS.allN_spec kr1_t j hj)
  refine ⟨fix_iff, ?_, ?_, fun j hj => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [fi24Ca_eq]
    exact comm_of (by decide +kernel) cmA_t
  · rw [fi24Cb_eq]
    exact comm_of (by decide +kernel) cmB_t
  · rw [kstrong_get' (by norm_num) hj]
    exact kr0 j hj
  · rw [kstrong_get' (by norm_num) hj]
    exact kr1 j hj
  · rw [fi24Ca_eq]
    exact act_of (by decide +kernel) (by norm_num) kr0 plA_t j hj
  · rw [fi24Cb_eq]
    exact act_of (by decide +kernel) (by norm_num) kr1 plB_t j hj

end Group

end CertificateChecks.KernelSpor.Fi24R2W

end
