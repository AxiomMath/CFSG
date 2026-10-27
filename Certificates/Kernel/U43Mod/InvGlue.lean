
module

public import Certificates.Kernel.U43Mod.InvChecks
public import Certificates.Kernel.U43Mod.LieOddSep
public import Certificates.Kernel.U43Mod.Glue
public import CFSG.Certificates.Kernel.U43Mod.InvSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Inv

open CFSG.KC.Enum CFSG.KC.U43Inv CFSG.KS CFSG.KS.U43Mod CFSG.KS.U43Inv CFSG.KS.U43Mod.LieOdd
  CertificateChecks.KernelU43Mod CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.Sporadic.SmallOddCore

theorem bNot_iff {b : Bool} : bNot b = true ↔ b = false := by cases b <;> simp [bNot]

theorem beq_false_iff {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, beq_iff]

theorem base3_spec {f g : ℕ → ℕ} (h : base3 f g = true) : f 0 = g 0 ∧ f 1 = g 1 ∧ f 9 = g 9 := by
  unfold base3 at h
  simp only [bAnd_iff, beq_iff] at h
  exact h

theorem f2Rec_spec {E Ei : ℕ → ℕ → ℕ} {A : ℕ → ℕ} {n k x d : ℕ} (h : f2Rec E Ei A n k x d = true) :
    base3 (E k) (fun p => p) = true ∨ (∃ q < 820, E k (E k q) ≠ q) ∨ base3 (E k) A = true ∨
      (x < n ∧ ∃ q < 820, E k (E x (E k (Ei x q))) ≠ E x (E k (Ei x (E k q)))) := by
  unfold f2Rec at h
  rw [strictB_eq, strictB_eq] at h
  generalize fld(d, nat_lit 0, nat_lit 3) = t at h
  generalize fld(d, nat_lit 2, nat_lit 1023) = q at h
  cases h0 : Nat.beq t 0 <;> rw [h0] at h <;> dsimp only at h
  · cases h1 : Nat.beq t 1 <;> rw [h1] at h <;> dsimp only at h
    · cases h2 : Nat.beq t 2 <;> rw [h2] at h <;> dsimp only at h
      · simp only [bAnd_iff, blt_iff, bNot_iff, beq_false_iff] at h
        exact Or.inr (Or.inr (Or.inr ⟨h.1, q, h.2.1, h.2.2⟩))
      · exact Or.inr (Or.inr (Or.inl h))
    · simp only [bAnd_iff, blt_iff, bNot_iff, beq_false_iff] at h
      exact Or.inr (Or.inl ⟨q, h.1, h.2⟩)
  · exact Or.inl h

theorem hsep (g h : X₀) (e0 : (psi g ⟨0, by norm_num⟩ : ℕ) = psi h ⟨0, by norm_num⟩)
    (e1 : (psi g ⟨1, by norm_num⟩ : ℕ) = psi h ⟨1, by norm_num⟩)
    (e9 : (psi g ⟨9, by norm_num⟩ : ℕ) = psi h ⟨9, by norm_num⟩) : g = h :=
  psi_sep g h (Fin.ext e0) (Fin.ext e1) (Fin.ext e9)

theorem sep_of_base3 {f f' : ℕ → ℕ} {g h : X₀} (hf : ∀ q (hq : q < 820), f q = (psi g ⟨q, hq⟩ : ℕ))
    (hf' : ∀ q (hq : q < 820), f' q = (psi h ⟨q, hq⟩ : ℕ)) (hb : base3 f f' = true) : g = h := by
  obtain ⟨b0, b1, b9⟩ := base3_spec hb
  exact hsep g h (by rw [← hf, ← hf', b0]) (by rw [← hf, ← hf', b1]) (by rw [← hf, ← hf', b9])

theorem GA0_eq (q : ℕ) (hq : q < 820) : GA 0 q = (psi xElt ⟨q, hq⟩ : ℕ) := by
  rw [GA_eq (by norm_num) q hq, CP_zero]

theorem LP_eq (l q : ℕ) (hq : q < 820) : LP l q = (psi (letElt l) ⟨q, hq⟩ : ℕ) := by
  by_cases h0 : l = 0
  · subst h0
    change GA 0 q = _
    rw [GA0_eq q hq]
    simp [letElt]
  by_cases h1 : l = 1
  · subst h1
    change GA 1 q = _
    rw [GA_eq (by norm_num) q hq, CP_one]
    simp [letElt]
  by_cases h2 : l = 2
  · subst h2
    change GAi 0 q = _
    rw [(letRep_GA (by norm_num) q hq).2, CP_zero]
    simp [letElt]
  unfold LP
  rw [beq_false h0, beq_false h1, beq_false h2]
  dsimp only
  rw [(letRep_GA (by norm_num) q hq).2, CP_one]
  simp [letElt, h0, h1, h2]

theorem hGenWords_len : hGenWords.length = 6 := by decide

theorem hGensG_len : hGensG.length = 6 := by simp [hGensG, hGenWords_len]

theorem hGens_len : hGens.length = 6 := by simp [hGens, hGenWords_len]

theorem hGensG_get {j : ℕ} (hj : j < 6) : hGensG.getD j 1 = wordElt hGenWords[j]! := by
  have hj' : j < hGenWords.length := by rw [hGenWords_len]; exact hj
  rw [hGensG, getD_map_lt _ _ hj', getElem!_pos hGenWords j hj']

theorem LT_eq {j : ℕ} (hj : j < 6) (q : ℕ) (hq : q < 820) :
    pg 10 1023 (LT (2 * j + 1)) q = (psi (hGensG.getD j 1) ⟨q, hq⟩ : ℕ) ∧
      pg 10 1023 (LT (2 * j)) q = (psi (hGensG.getD j 1)⁻¹ ⟨q, hq⟩ : ℕ) := by
  have hw := (lwalk_spec kL).2 j hj
  have hL : ∀ p (hp : p < 820), pg 10 1023 (LT (2 * j + 1)) p = (psi (hGensG.getD j 1) ⟨p, hp⟩ : ℕ)
      ∧ pg 10 1023 (LT (2 * j)) (pg 10 1023 (LT (2 * j + 1)) p) = p := by
    intro p hp
    have h1 := allN_spec hw p hp
    rw [strictB_eq, bAnd_iff, beq_iff, beq_iff] at h1
    have e : Nat.shiftLeft j 1 = 2 * j := by
      change j <<< 1 = 2 * j
      rw [Nat.shiftLeft_eq]
      ring
    rw [e] at h1
    obtain ⟨h2, h3⟩ := h1
    refine ⟨?_, h3⟩
    rw [h2, mwv_eq LP_eq _ p hp, hGensG_get hj]
  refine ⟨(hL q hq).1, ?_⟩
  have hp : (psi (hGensG.getD j 1)⁻¹ ⟨q, hq⟩ : ℕ) < 820 := Fin.is_lt _
  have h2 := (hL _ hp).2
  rw [(hL _ hp).1, Fin.eta, map_inv, ← Equiv.Perm.mul_apply, mul_inv_cancel,
    Equiv.Perm.one_apply] at h2
  rw [map_inv]
  exact h2

theorem half_cases {l : ℕ} : ∃ j, (l = 2 * j ∧ l % 2 = 0 ∧ l / 2 = j) ∨
    (l = 2 * j + 1 ∧ l % 2 = 1 ∧ l / 2 = j) := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' l
  · exact ⟨j, Or.inl ⟨hj, by omega, by omega⟩⟩
  · exact ⟨j, Or.inr ⟨hj, by omega, by omega⟩⟩

theorem xor_one_even {j : ℕ} (hj : j < 6) : Nat.xor (2 * j) 1 = 2 * j + 1 := by
  interval_cases j <;> rfl

theorem xor_one_odd {j : ℕ} (hj : j < 6) : Nat.xor (2 * j + 1) 1 = 2 * j := by
  interval_cases j <;> rfl

theorem hG_H : ∀ l < 12, ∀ q (hq : q < 820), GkH l q = (psi (sF hGensG l)⁻¹ ⟨q, hq⟩ : ℕ) ∧
    GrH l q = (psi (sF hGensG l) ⟨q, hq⟩ : ℕ) := by
  intro l hl q hq
  obtain ⟨j, ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩⟩ := half_cases (l := l)
  · have hj : j < 6 := by omega
    unfold GkH GrH sF
    rw [if_pos h1, h2, xor_one_even hj]
    exact ⟨(LT_eq hj q hq).2, (LT_eq hj q hq).1⟩
  · have hj : j < 6 := by omega
    unfold GkH GrH sF
    rw [if_neg (by omega), h2, xor_one_odd hj, inv_inv, map_inv]
    exact ⟨(LT_eq hj q hq).1, by rw [← map_inv]; exact (LT_eq hj q hq).2⟩

theorem hElt_eq (k : ℕ) : hElt k = treeG 1 (mulStepG hGensG) hPar hLab 12 fuel k := by
  unfold hElt
  rw [hGensG_len]

theorem kdep_le {R : ℕ → ℕ} {n nl : ℕ} {Gk : ℕ → ℕ → ℕ} (hT : kTree R n nl Gk = true) :
    ∀ k < n, kdep (R k) ≤ 32 := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have := (kRecOK_zero (allN_spec hT 0 hk)).1
    omega
  · have := (kRecOK_succ (by omega) (allN_spec hT k hk)).2.2.2.1
    omega

theorem hFacts : ∀ k < 1152, KeyOf (HR k) (hElt k)⁻¹ ∧ WalkOf HR GrH GkH k (hElt k) := by
  intro k hk
  rw [hElt_eq]
  exact key_tree hG_H (by norm_num) kHtree (fldsAre_spec kHpar) (fldsAre_spec kHlab) k hk

theorem EH_eq {k : ℕ} (hk : k < 1152) (q : ℕ) (hq : q < 820) :
    EH k q = (psi (hElt k) ⟨q, hq⟩ : ℕ) ∧ EHi k q = (psi (hElt k)⁻¹ ⟨q, hq⟩ : ℕ) :=
  (hFacts k hk).2 32 (kdep_le kHtree k hk) q hq

theorem gens_fact : ∀ j < hGens.length, isInvA 820 hGens[j]! (invCand 820 hGens[j]!) = true ∧
    eqA 820 (compA 820 hGens[j]! tabA) (compA 820 tabA hGens[j]!) = true := by
  intro j hj
  have hj' : j < hGenWords.length := by simpa [hGens] using hj
  have hr : Rep 820 hGens[j]! (psi (wordElt hGenWords[j]!)) := by
    rw [hGens, getElem!_map_lt _ _ hj', getElem!_pos hGenWords j hj']
    exact rep_wordTab _
  refine ⟨isInvA_invCand hr, ?_⟩
  rw [eqA_iff (rep_compA hr rep_tabA) (rep_compA rep_tabA hr), ← map_mul, ← map_mul]
  have hw := (lwalk_spec kGens).2 j (by rw [hGenWords_len] at hj'; exact hj')
  refine congrArg psi (sep_of_base3 (f := fun q => mwv LP hGenWords[j]! (GA 0 q))
    (f' := fun q => GA 0 (mwv LP hGenWords[j]! q)) (fun q hq => ?_) (fun q hq => ?_) hw)
  · rw [GA0_eq q hq, mwv_eq LP_eq _ _ (Fin.is_lt _), Fin.eta, map_mul, Equiv.Perm.mul_apply]
  · rw [mwv_eq LP_eq _ q hq, GA0_eq _ (Fin.is_lt _), Fin.eta, map_mul, Equiv.Perm.mul_apply]

theorem rep_hGens' : ∀ j < hGensG.length, Rep 820 hGens[j]! (psi (hGensG.getD j 1)) := by
  intro j hj
  have hj' : j < hGenWords.length := by simpa [hGensG] using hj
  rw [hGens, getElem!_map_lt _ _ hj', hGensG, getD_map_lt _ _ hj']
  exact rep_wordTab _

theorem rep_hTab' (k : ℕ) : Rep 820 (hTab k) (psi (hElt k)) := by
  have hnl : 0 < 2 * hGensG.length := by rw [hGensG_len]; norm_num
  unfold hTab hElt
  rw [hGens_length]
  exact rep_treeG rep_one hnl (fun t g l hl h => rep_mulStep hGens_length rep_hGens'
    (fun j hj => (gens_fact j (by rw [hGens_length]; exact hj)).1) t g l hl h) hPar hLab fuel k

theorem hclosed_fact : closedOK hTab hTbl 1152 (2 * hGens.length) (mulStep hGens) = true := by
  rw [hGens_len]
  refine closedOK_of (x := fun k => psi (hElt k)) (sG := fun p l => p * psi (sF hGensG l))
    (fun k _ => rep_hTab' k) (fun k _ l hl => ?_) (fun k hk l hl => ?_)
  · have h := rep_mulStep hGens_length rep_hGens'
      (fun j hj => (gens_fact j (by rw [hGens_length]; exact hj)).1) (hTab k) (hElt k) l
      (by rw [hGensG_len]; exact hl) (rep_hTab' k)
    rwa [mulStepG_eq, map_mul] at h
  · obtain ⟨h1, h2⟩ := key_clos (by norm_num) (fun k hk => (hFacts k hk).1)
      (fun l hl q hq => (hG_H l hl q hq).1) hsep kHclos k hk l hl
    refine ⟨h1, ?_⟩
    change psi (hElt _) = psi (hElt k) * psi (sF hGensG l)
    rw [h2, map_mul]

theorem hinj : ∀ i < 1152, ∀ j < 1152, hElt i = hElt j → i = j :=
  key_inj (by norm_num) (fun k hk => (hFacts k hk).1) kHord

theorem hdist_fact : distinctOK hTab 1152 = true :=
  distinctOK_of_sep psi_sep (fun k _ => rep_hTab' k) hinj

theorem card_hSub' : Nat.card hSub = 1152 := by
  obtain ⟨hmem, hsurj, hinj'⟩ := enum_spec hGens_length rep_hGens'
    (fun j hj => (gens_fact j (by rw [hGens_length]; exact hj)).1)
    (by rw [hGensG_len]; norm_num) (by norm_num) hclosed_fact hdist_fact
  have : Function.Bijective (fun k : Fin 1152 => (⟨hElt k, hmem k⟩ : hSub)) := by
    constructor
    · intro i j hij
      exact Fin.ext (hinj' i i.2 j j.2 (congrArg Subtype.val hij))
    · intro h
      obtain ⟨k, hk, hkh⟩ := hsurj h h.2
      exact ⟨⟨k, hk⟩, Subtype.ext hkh⟩
  rw [← Nat.card_eq_of_bijective _ this]
  simp

theorem hSub_le_centralizer' : hSub ≤ Subgroup.centralizer ({xElt} : Set X₀) := by
  unfold hSub
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hj' : j < hGens.length := by rw [hGens_length]; exact hj
  have hr := rep_hGens' j hj
  rw [List.getD_eq_getElem _ _ hj] at hr
  have heq := (eqA_iff (rep_compA hr rep_tabA) (rep_compA rep_tabA hr)).1 (gens_fact j hj').2
  rw [← map_mul, ← map_mul] at heq
  exact (psi_injective heq).symm

theorem pGenIdx_len : pGenIdx.length = 3 := by decide

theorem pGenIdx_lt : ∀ j < 3, pGenIdx.getD j 0 < 1152 := by decide

theorem pGensG_len : pGensG.length = 3 := by simp [pGensG, pGenIdx_len]

theorem pGensG_get {j : ℕ} (hj : j < 3) : pGensG.getD j 1 = hElt (pIdx j) := by
  have hj' : j < pGenIdx.length := by rw [pGenIdx_len]; exact hj
  rw [pGensG, getD_map_lt _ _ hj', pIdx, List.getD_eq_getElem _ _ hj']

theorem hG_P : ∀ l < 6, ∀ q (hq : q < 820), GkP l q = (psi (sF pGensG l)⁻¹ ⟨q, hq⟩ : ℕ) ∧
    GrP l q = (psi (sF pGensG l) ⟨q, hq⟩ : ℕ) := by
  intro l hl q hq
  have e1 : Nat.shiftRight l 1 = l / 2 := by
    change l >>> 1 = l / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  have e2 : Nat.land l 1 = l % 2 := Nat.and_one_is_mod l
  have hj : l / 2 < 3 := by omega
  have hi : pIdx (l / 2) < 1152 := pGenIdx_lt _ hj
  unfold GkP GrP sF
  rw [e1, e2, pGensG_get hj]
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · rw [h, if_pos rfl]
    exact ⟨(EH_eq hi q hq).2, (EH_eq hi q hq).1⟩
  · rw [h, if_neg (by omega), inv_inv]
    exact ⟨(EH_eq hi q hq).1, by rw [map_inv]; rw [← map_inv]; exact (EH_eq hi q hq).2⟩

theorem pElt_eq (k : ℕ) : pElt k = treeG 1 (mulStepG pGensG) pPar pLab 6 fuel k := by
  unfold pElt
  rw [pGensG_len]

theorem pFacts : ∀ k < 128, KeyOf (PR k) (pElt k)⁻¹ ∧ WalkOf PR GrP GkP k (pElt k) := by
  intro k hk
  rw [pElt_eq]
  exact key_tree hG_P (by norm_num) kPtree (fldsAre_spec kPpar) (fldsAre_spec kPlab) k hk

theorem rep_pGens' : ∀ j < pGensG.length, Rep 820 pGens[j]! (psi (pGensG.getD j 1)) := by
  intro j hj
  have hj' : j < pGenIdx.length := by simpa [pGensG] using hj
  rw [pGens, getElem!_map_lt _ _ hj', pGensG, getD_map_lt _ _ hj']
  exact rep_hTab' _

theorem pinv_fact : ∀ j < pGens.length, isInvA 820 pGens[j]! (invCand 820 pGens[j]!) = true :=
  fun j hj => isInvA_invCand (rep_pGens' j (by rw [← pGens_length]; exact hj))

theorem rep_pTab' (k : ℕ) : Rep 820 (pTab k) (psi (pElt k)) := by
  have hnl : 0 < 2 * pGensG.length := by rw [pGensG_len]; norm_num
  unfold pTab pElt
  rw [pGens_length]
  exact rep_treeG rep_one hnl (fun t g l hl h => rep_mulStep pGens_length rep_pGens'
    (fun j hj => pinv_fact j (by rw [pGens_length]; exact hj)) t g l hl h) pPar pLab fuel k

theorem pGens_len : pGens.length = 3 := by simp [pGens, pGenIdx_len]

theorem pclosed_fact : closedOK pTab pTbl 128 (2 * pGens.length) (mulStep pGens) = true := by
  rw [pGens_len]
  refine closedOK_of (x := fun k => psi (pElt k)) (sG := fun p l => p * psi (sF pGensG l))
    (fun k _ => rep_pTab' k) (fun k _ l hl => ?_) (fun k hk l hl => ?_)
  · have h := rep_mulStep pGens_length rep_pGens'
      (fun j hj => pinv_fact j (by rw [pGens_length]; exact hj)) (pTab k) (pElt k) l
      (by rw [pGensG_len]; exact hl) (rep_pTab' k)
    rwa [mulStepG_eq, map_mul] at h
  · obtain ⟨h1, h2⟩ := key_clos (by norm_num) (fun k hk => (pFacts k hk).1)
      (fun l hl q hq => (hG_P l hl q hq).1) hsep kPclos k hk l hl
    refine ⟨h1, ?_⟩
    change psi (pElt _) = psi (pElt k) * psi (sF pGensG l)
    rw [h2, map_mul]

theorem pdist_fact : distinctOK pTab 128 = true :=
  distinctOK_of_sep psi_sep (fun k _ => rep_pTab' k)
    (key_inj (by norm_num) (fun k hk => (pFacts k hk).1) kPord)

theorem cFacts : ∀ k < 2835, ∀ q, (orM (cf (CR k)) 20).testBit q = true ↔
    ∃ hq : q < 820, psi (cElt k) ⟨q, hq⟩ = ⟨q, hq⟩ :=
  fix_tree (fun l _ q hq => LP_eq l q hq) GA0_eq (by norm_num) kCtree kCfix
    (fldsAre_spec kCpar) (fldsAre_spec kClab)

theorem cinj : ∀ i < 2835, ∀ j < 2835, cElt i = cElt j → i = j :=
  fix_inj (by norm_num) cFacts kCord

theorem cdist_fact : distinctOK cTab 2835 = true :=
  distinctOK_of_sep psi_sep (fun k _ => rep_cTab k) cinj

theorem conj_eq : ∀ u ∈ conjugatesOf xElt, ∃ j < 2835, cElt j = u := by
  have hfin : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  set S : Set X₀ := cElt '' ((Finset.range 2835 : Finset ℕ) : Set ℕ)
  have hsub : S ⊆ conjugatesOf xElt := by
    rintro _ ⟨k, -, rfl⟩
    obtain ⟨d, hd⟩ := cElt_conj k
    change IsConj xElt (cElt k)
    rw [isConj_iff]
    exact ⟨d, hd.symm⟩
  have hS : S.ncard = 2835 := by
    have hinj' : Set.InjOn cElt ((Finset.range 2835 : Finset ℕ) : Set ℕ) := by
      intro i hi j hj hij
      exact cinj i (by simpa using hi) j (by simpa using hj) hij
    rw [hinj'.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  have hle : (conjugatesOf xElt).ncard ≤ 2835 := by
    have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({xElt} : Set X₀))
    rw [Subgroup.index_centralizer_eq_ncard, card_X₀] at h1
    have h2 : 1152 ≤ Nat.card (Subgroup.centralizer ({xElt} : Set X₀)) := by
      rw [← card_hSub']
      exact Subgroup.card_le_of_le hSub_le_centralizer'
    nlinarith
  have heq : S = conjugatesOf xElt :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hS]; exact hle) (Set.toFinite _)
  intro u hu
  rw [← heq] at hu
  obtain ⟨j, hj, rfl⟩ := hu
  exact ⟨j, by simpa using hj, rfl⟩

section Fuse

theorem invol_conj {u : X₀} (h2 : u * u = 1) (h1 : u ≠ 1) : u ∈ conjugatesOf xElt := by
  have hP : psi u ∈ P := psi_mem_P u
  have hu2 : psi u * psi u = 1 := by rw [← map_mul, h2, map_one]
  have hu1 : psi u ≠ 1 := fun e => h1 (psi_injective (by rw [e, map_one]))
  obtain ⟨c, hc, hcu⟩ := invol_mem_classA hP hu2 hu1
  have hrange : P ≤ psi.range := by
    rw [P_eq_closure, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨xElt, rfl⟩
    · exact ⟨yElt, rfl⟩
  obtain ⟨d, rfl⟩ := hrange hc
  have e : u = d * xElt * d⁻¹ := by
    apply psi_injective
    rw [hcu, CP_zero, map_mul, map_mul, map_inv]
  change IsConj xElt u
  rw [isConj_iff]
  exact ⟨d, e.symm⟩

theorem fuse_fact : ∀ k < 128, fuseOK k = true := fun k _ =>
  fuseOK_of (rep_pTab' k) fun h2 h1 => conj_eq _ (invol_conj h2 h1)

end Fuse

theorem f2_fact : ∀ k < 1152, f2OK k = true := by
  intro k hk
  refine f2OK_of (fun j => rep_hTab' j) fun h2 h1 hx => ?_
  have hw := (lwalk_spec kF2).2 k hk
  rw [Array.getElem!_toList] at hw
  rcases f2Rec_spec hw with hb | ⟨q, hq, hb⟩ | hb | ⟨hlt, q, hq, hb⟩
  · exact absurd (sep_of_base3 (fun q hq => (EH_eq hk q hq).1) (fun q hq => by simp) hb) h1
  · exfalso
    apply hb
    rw [(EH_eq hk q hq).1, (EH_eq hk _ (Fin.is_lt _)).1, Fin.eta, ← Equiv.Perm.mul_apply,
      ← map_mul, h2, map_one]
    rfl
  · exact absurd (sep_of_base3 (fun q hq => (EH_eq hk q hq).1) GA0_eq hb) hx
  · refine ⟨hlt, fun e => hb ?_⟩
    set c := hElt f2Wit[k]!
    set b := hElt k
    have hu : ∀ p (hp : p < 820), EH f2Wit[k]! (EH k (EHi f2Wit[k]! p)) =
        (psi (c * b * c⁻¹) ⟨p, hp⟩ : ℕ) := by
      intro p hp
      rw [(EH_eq hlt p hp).2, (EH_eq hk _ (Fin.is_lt _)).1, Fin.eta, (EH_eq hlt _ (Fin.is_lt _)).1,
        Fin.eta, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, map_inv]
    rw [hu q hq, (EH_eq hk _ (Fin.is_lt _)).1, Fin.eta, (EH_eq hk q hq).1, hu _ (Fin.is_lt _),
      Fin.eta, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, e]

theorem g0Word_lt : ∀ l ∈ g0Word, l < 4 := by decide

theorem g0_fact : g0OK = true := by
  apply g0OK_of
  have hfin : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  set z := xElt * (g0Elt * xElt * g0Elt⁻¹)
  have h := kG0
  unfold g0Chk at h
  rw [bAnd_iff, blt_iff] at h
  obtain ⟨hq0, hall⟩ := h
  have hz : ∀ q (hq : q < 820), GA 0 (mwv LP g0Word (GA 0 (mwvI LP g0Word q))) =
      (psi z ⟨q, hq⟩ : ℕ) := by
    intro q hq
    rw [mwvI_eq LP_eq _ g0Word_lt q hq, GA0_eq _ (Fin.is_lt _), Fin.eta,
      mwv_eq LP_eq _ _ (Fin.is_lt _), Fin.eta, GA0_eq _ (Fin.is_lt _), Fin.eta]
    simp only [z, g0Elt, map_mul, map_inv, Equiv.Perm.mul_apply]
  have hit : ∀ m, Nat.rec (motive := fun _ => ℕ) (MR 0)
      (fun _ ih => GA 0 (mwv LP g0Word (GA 0 (mwvI LP g0Word ih)))) m =
        (psi (z ^ m) ⟨MR 0, hq0⟩ : ℕ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      change GA 0 (mwv LP g0Word (GA 0 (mwvI LP g0Word (Nat.rec (motive := fun _ => ℕ) (MR 0)
        (fun _ ih => GA 0 (mwv LP g0Word (GA 0 (mwvI LP g0Word ih)))) m)))) = _
      rw [ih, hz _ (Fin.is_lt _), Fin.eta, pow_succ', map_mul psi z (z ^ m), Equiv.Perm.mul_apply]
  by_contra hlt
  push Not at hlt
  have hpos : 0 < orderOf z := orderOf_pos _
  have h5 : orderOf z - 1 < 5 := by omega
  have h1 := allN_spec hall (orderOf z - 1) h5
  rw [bNot_iff, beq_false_iff] at h1
  apply h1
  have e : Nat.succ (orderOf z - 1) = orderOf z := by omega
  rw [e, hit, pow_orderOf_eq_one, map_one]
  rfl

theorem hpos_fact : 0 < hGens.length := by rw [hGens_len]; norm_num

theorem ppos_fact : 0 < pGens.length := by rw [pGens_len]; norm_num

theorem checkFacts' : CheckFacts :=
  ⟨gens_fact, hpos_fact, hdist_fact, hclosed_fact, ppos_fact, pinv_fact, pdist_fact,
    pclosed_fact, cdist_fact, fuse_fact, f2_fact, g0_fact⟩

theorem u43InvCheck_ok : u43InvCheck () = true := u43InvCheck_of checkFacts'

end CertificateChecks.KernelU43Inv

end
