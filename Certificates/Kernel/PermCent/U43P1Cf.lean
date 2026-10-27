module

public import Certificates.Kernel.PermCent.U43P1Rep
public import Certificates.Kernel.PermCent.U43P1Cfg

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1 CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin Subgroup

theorem cfgOK_spec {T : ℕ → ℕ} {cls : ℕ → ℕ → ℕ} {sz : ℕ → ℕ} {inner : Bool} {mem : ℕ → Bool}
    {Ls : List ℕ} {d dI : ℕ} {W : List ℕ} (h : cfgOK T cls sz inner mem Ls d dI W = true) :
    ∀ i < W.length, invol (T i) = true → (inner = true ∧ mem (T i) = true) ∨
      (∀ l ∈ Ls, notOrd8 (pc (T i) l) = true) ∨ (∃ c < 2, ∃ j < sz c, cls c j = T i) ∨
      (∃ c < 2, ∃ j < sz c, cls c j = pc dI (pc (T i) d)) := by
  intro i hi hv
  rw [cfgOK, List.all_eq_true] at h
  have hm : (W[i], i) ∈ W.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi)
  have h1 := h _ hm
  dsimp only at h1
  cases e0 : Nat.beq W[i] 0
  · rw [e0, cond_false] at h1
    cases e1 : Nat.beq W[i] 1
    · rw [e1, cond_false] at h1
      cases e2 : Nat.beq W[i] 2
      · rw [e2, cond_false] at h1
        cases e3 : Nat.blt ((W[i] - 3) / 65536) 2
        · rw [e3, cond_false] at h1
          obtain ⟨hc, hj, hx⟩ := inCls_spec h1
          refine Or.inr (Or.inr (Or.inr ⟨_, ?_, _, hj, hx⟩))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          omega
        · rw [e3, cond_true] at h1
          obtain ⟨-, hj, hx⟩ := inCls_spec h1
          rw [Nat.blt_eq] at e3
          exact Or.inr (Or.inr (Or.inl ⟨_, e3, _, hj, hx⟩))
      · rw [e2, cond_true, List.all_eq_true] at h1
        exact Or.inr (Or.inl h1)
    · rw [e1, cond_true, Bool.and_eq_true] at h1
      exact Or.inl h1
  · rw [e0, cond_true, hv] at h1
    exact Bool.noConfusion h1

theorem notOrd8_spec {p : ℕ} {σ : Equiv.Perm (Fin 820)} (hp : PRep 820 10 p σ)
    (h : notOrd8 p = true) : orderOf σ ≠ 8 := by
  intro h8
  have p2 := prep_pc hp hp
  have p4 := prep_pc p2 p2
  have p8 := prep_pc p4 p4
  have h' : (isId (pc (pc p p) (pc p p)) ||
      !isId (pc (pc (pc p p) (pc p p)) (pc (pc p p) (pc p p)))) = true := h
  have e8 : σ ^ 8 = 1 := h8 ▸ pow_orderOf_eq_one σ
  rw [Bool.or_eq_true] at h'
  rcases h' with h1 | h1
  · have e4 := eq_one_of_isId p4 h1
    have e4' : σ ^ 4 = 1 := by
      rw [← e4]
      calc σ ^ 4 = σ ^ (1 + 1 + 1 + 1) := rfl
        _ = σ * σ * (σ * σ) := by simp only [pow_add, pow_one, mul_assoc]
    have hd := orderOf_dvd_of_pow_eq_one e4'
    rw [h8] at hd
    norm_num at hd
  · rw [Bool.not_eq_true'] at h1
    have hs8 : σ * σ * (σ * σ) * (σ * σ * (σ * σ)) = 1 := by
      rw [← e8]
      calc σ * σ * (σ * σ) * (σ * σ * (σ * σ)) = σ ^ (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) := by
            simp only [pow_add, pow_one, mul_assoc]
        _ = σ ^ 8 := rfl
    rw [hs8] at p8
    rw [isId_of_prep p8] at h1
    exact Bool.noConfusion h1

theorem sq_mem_of_coset {w u : Equiv.Perm (Fin 820)}
    (hu : u ∈ normalizer (psi.range : Set (Equiv.Perm (Fin 820)))) (huu : u * u = 1)
    (h : w * u⁻¹ ∈ psi.range) : w * w ∈ psi.range := by
  have e : w * w = w * u⁻¹ * (u * (w * u⁻¹) * u⁻¹) * (u * u) := by group
  rw [e, huu, mul_one]
  exact mul_mem h ((mem_normalizer_iff.mp hu _).mp h)

theorem conj_outer {U : Equiv.Perm (Fin 820)} (hUU : U * U = 1) (hU : U ∉ psi.range) :
    dK * U * dK⁻¹ * (dK * U * dK⁻¹) = 1 ∧ dK * U * dK⁻¹ ∉ psi.range := by
  refine ⟨by rw [show dK * U * dK⁻¹ * (dK * U * dK⁻¹) = dK * (U * U) * dK⁻¹ by group, hUU]; group,
    fun h => hU ?_⟩
  have h1 := (mem_normalizer_iff.mp (inv_mem dK_mem_normalizer) _).mp h
  rwa [show dK⁻¹ * (dK * U * dK⁻¹) * dK⁻¹⁻¹ = U by group] at h1

theorem fac720 : (720 : ℕ).factorization 2 = 4 := by
  have h : (720 : ℕ) = 2 ^ 4 * 45 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem fac1440 : (2 * 720 : ℕ).factorization 2 = 5 := by
  have h : (2 * 720 : ℕ) = 2 ^ 5 * 45 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem cfg_coset {c : ℕ} (hc : c < 6)
    {L : Subgroup (Equiv.Perm (Fin 820))}
    (hLeq : CFSG.ComponentClassification.HarrisLit.Q81.oddPart
      (psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) = L)
    (hCcard : Nat.card ↥(psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) = 720)
    {kw dw : ℕ} {εw : Bool} (hsw : USpec kw dw)
    (hwt : Cover.commOK (pk kw εw) (clsT c (clsR c)) = true)
    {l : List (ℕ × Bool)} {ng N LL KK : ℕ} {G T E D S : ℕ → ℕ}
    (hw : (eK kw εw ∈ psi.range ∧ N = 16) ∨
      (eK kw εw ∉ psi.range ∧ eK kw εw * eK kw εw ∈ psi.range ∧ N = 32))
    (hG : gensOK l G = true)
    (hl : ∀ x ∈ l, detOf x.1 ≠ 0 ∧ ((x.2 = false ∧ detOf x.1 = 3) ∨ (x.2 = εw ∧ detOf x.1 = dw)))
    (hng : ng = l.length) (hcl : ∀ i, i < LL * KK → closPtL 820 10 ng N G T E i = true)
    (htr : ∀ i, i < LL * KK → treePt ng N 0 E D i = true) (hNL : N ≤ LL * KK)
    (h0 : Nat.beq (T 0) (pidn 820 10) = true)
    (hK : distinctK N (fun i => pkeyK 820 10 baseT (T i)) S = true)
    (hcomT : ∀ j < l.length, Cover.commOK (G j) (clsT c (clsR c)) = true)
    {inner : Bool} {mem : ℕ → Bool} {Ls W : List ℕ}
    (hcfg : cfgOK T a6T a6N inner mem Ls (pk cDi false) (pk cDmi false) W = true)
    (hW : W.length = N) (hinner : inner = true → eK kw εw ∉ psi.range)
    (hmem : ∀ i < N, mem (T i) = true → ∀ σ, PRep 820 10 (T i) σ → σ ∈ psi.range)
    (hLs : ∀ y ∈ L, orderOf y = 2 → ∃ p ∈ Ls, PRep 820 10 p y)
    (ha6 : ∀ c' < 2, ∀ j < a6N c', ∀ σ, PRep 820 10 (a6T c' j) σ → A6Normal psi.range σ) :
    ∀ v, orderOf v = 2 → v * tRep c = tRep c * v → v * (eK kw εw)⁻¹ ∈ psi.range →
      (∃ y ∈ L, orderOf y = 2 ∧ orderOf (v * y) = 8) → A6Normal psi.range v := by
  intro v hv2 hvt hvw hl8
  have hpw := prep_pk' hsw εw
  have hwt' : eK kw εw * tRep c = tRep c * eK kw εw := comm_of_commOK hpw (root_prep c hc) hwt
  have hwN := eK_mem_normalizer' hsw εw
  have hwc : eK kw εw ∈ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) :=
    mem_centralizer_singleton_iff.mpr hwt'
  have hN0 : 0 < N := by
    rcases hw with ⟨-, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num
  obtain ⟨hcard, hpts, -⟩ := enum_group hG (fun x hx => (hl x hx).1) hng hcl htr hNL hN0 h0
    baseT_lt hK
  have pG := prep_gensOK hG (fun x hx => (hl x hx).1)
  have hTD : closure (gK l '' {k | k < ng}) ≤
      psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) ⊔ zpowers (eK kw εw) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < l.length := hng ▸ hk
    have hgc : gK l k ∈ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) :=
      mem_centralizer_singleton_iff.mpr (comm_of_commOK (pG k hk') (root_prep c hc) (hcomT k hk'))
    refine mem_sup_of_coset ?_
    rcases gK_mem_or hsw hl k hk' with h | h
    · exact Or.inl (mem_inf.mpr ⟨h, hgc⟩)
    · exact Or.inr (mem_inf.mpr ⟨h, mul_mem hgc (inv_mem hwc)⟩)
  have hTcard : Nat.card (closure (gK l '' {k | k < ng})) = 2 ^ (Nat.card ↥(psi.range ⊓
      centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) ⊔ zpowers (eK kw εw))).factorization 2 := by
    rw [hcard]
    rcases hw with ⟨hwA, hN16⟩ | ⟨hwA, hww, hN32⟩
    · rw [sup_eq_left.2 ((zpowers_le).2 (mem_inf.mpr ⟨hwA, hwc⟩)), hCcard, fac720, hN16]
      norm_num
    · have hwC : eK kw εw ∉ psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) :=
        fun h => hwA (mem_inf.mp h).1
      have hwwC : eK kw εw * eK kw εw ∈
          psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) :=
        mem_inf.mpr ⟨hww, mul_mem hwc hwc⟩
      have hwNC : eK kw εw ∈ normalizer ((psi.range ⊓
          centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) : Subgroup (Equiv.Perm (Fin 820))) :
            Set (Equiv.Perm (Fin 820))) := by
        have e : eK kw εw * tRep c * (eK kw εw)⁻¹ = tRep c := by
          rw [hwt', mul_assoc, mul_inv_cancel, mul_one]
        have h1 := inf_centralizer_conj_of_mem_normalizer psi.range hwN (tRep c)
        rw [e] at h1
        exact mem_normalizer_iff_map_conj_eq.mpr h1.symm
      rw [card_sup_zpowers_of_sq_mem hwNC hwwC hwC, hCcard, fac1440, hN32]
      norm_num
  refine config_of_sylow hLeq hwN hwt' hTD hTcard ?_ hv2 hvt hvw hl8
  intro v' hv' hv'2 hvA hl'
  obtain ⟨i, hi, hp⟩ := hpts v' hv'
  have hinv := (invol_iff hp).2 (mul_self_of_orderOf hv'2)
  rcases cfgOK_spec hcfg i (by rw [hW]; exact hi) hinv with ⟨hin, hm⟩ | h8 |
      ⟨c', hc', j, hj, e⟩ | ⟨c', hc', j, hj, e⟩
  · exact absurd (hvA.1 (hmem i hi hm v' hp)) (hinner hin)
  · obtain ⟨y, hy, hy2, hy8⟩ := hl'
    obtain ⟨q, hq, hpq⟩ := hLs y hy hy2
    exact absurd hy8 (notOrd8_spec (prep_pc hp hpq) (h8 q hq))
  · rw [← e] at hp
    exact ha6 c' hc' j hj v' hp
  · have hd : PRep 820 10 (pk cDi false) dK := prep_pk' spec_cDi false
    have hdi : PRep 820 10 (pk cDmi false) dK⁻¹ := by
      rw [d_facts.1]
      exact prep_pk' spec_cDmi false
    have hp' := prep_pc hdi (prep_pc hp hd)
    rw [← e] at hp'
    have h1 := a6Normal_conj dK_mem_normalizer (ha6 c' hc' j hj _ hp')
    rwa [show dK * (dK⁻¹ * (v' * dK)) * dK⁻¹ = v' by group] at h1

theorem none_of_noneIa {u : ℕ} {U : Equiv.Perm (Fin 820)}
    (hpu : PRep 820 10 u U) (h : noneIa u = true) {v : Equiv.Perm (Fin 820)}
    (hvt : v * tRep 5 = tRep 5 * v) (hvu : v * U⁻¹ ∈ psi.range) : False := by
  rw [noneIa, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hid, hany⟩ := h
  have hUU : U * U = 1 := eq_one_of_isId (prep_pc hpu hpu) hid
  have e : U * (tRep 5 * U) = (v * U⁻¹)⁻¹ * tRep 5 * (v * U⁻¹)⁻¹⁻¹ := by
    have hU : U⁻¹ = U := inv_eq_of_mul_eq_one_right hUU
    have hv : v * tRep 5 * v⁻¹ = tRep 5 := by rw [hvt, mul_assoc, mul_inv_cancel, mul_one]
    calc U * (tRep 5 * U) = U * tRep 5 * U⁻¹ := by rw [hU, mul_assoc]
      _ = (v * U⁻¹)⁻¹ * (v * tRep 5 * v⁻¹) * (v * U⁻¹)⁻¹⁻¹ := by group
      _ = _ := by rw [hv]
  obtain ⟨-, -, hall⟩ := cls_facts 5 (by norm_num)
  obtain ⟨j, hj, hpj⟩ := hall _ (inv_mem hvu)
  have hp := prep_pc hpu (prep_pc (root_prep 5 (by norm_num)) hpu)
  rw [e] at hp
  have hN : clsN 5 = 4536 := bindsC.2.2.2.2.2.2.1
  have hj' : j < 4536 := by rw [← hN]; exact hj
  have hcan := (closPt_spec (CIa.cl j (lt_of_lt_of_le hj' (by decide)))).1
  have hshr := (CFSG.KS.PF.canon_facts hcan).2.2.1
  have heq : CIa.T j = pc u (pc (clsT 5 (clsR 5)) u) :=
    CFSG.KS.PF.eq_of_fields (by norm_num) hshr (CFSG.KS.PF.pcomp_shr _ _ (by norm_num) (by norm_num))
      (fun i hi => (hpj ⟨i, hi⟩).trans (hp ⟨i, hi⟩).symm)
  have hT : (List.range 4536).any
      (fun j => Nat.beq (CIa.T j) (pc u (pc (clsT 5 (clsR 5)) u))) = true :=
    List.any_eq_true.2 ⟨j, List.mem_range.2 hj', by rw [heq]; exact Nat.beq_refl _⟩
  rw [hT] at hany
  exact Bool.noConfusion hany

end CertificateChecks.KernelPermCent.U43P1

end
