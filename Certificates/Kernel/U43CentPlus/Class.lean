module

public import Certificates.Kernel.U43CentPlus.Sound
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43CentPlus

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43CentPlus CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KS.U43Mod CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43
  CertificateChecks.KernelU43Mod CFSG.Sporadic.SmallOddCore Subgroup

theorem cRec_spec {n w m : ℕ} {Y R : ℕ → ℕ} {N k : ℕ} {E EI : ℕ → ℕ} {g h r : ℕ}
    (hr : cRec n w m Y R N k E EI g h r = true) :
    (cDep R r = 0 ∧ eq2 n w m (Y r) g h = true) ∨
      ∃ par lab, par < N ∧ lab < k ∧ cDep R par + 1 = cDep R r ∧
        eq3 n w m (Y r) (E lab) (Y par) (EI lab) = true := by
  unfold cRec at hr
  simp only [CFSG.KS.U43Mod.strictB_eq] at hr
  cases hb : Nat.beq (cDep R r) 0
  · right
    have h := CFSG.KC.EnumSound.bIf_false hb hr
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
    rw [blt_iff] at h1 h2
    have h3' := (CFSG.KC.EnumSound.beq_iff _ _).1 h3
    have hne : cDep R r ≠ 0 := fun e => by rw [e] at hb; exact absurd hb (by decide)
    refine ⟨_, _, h1, h2, ?_, h4⟩
    change cDep R _ = cDep R r - 1 at h3'
    omega
  · left
    exact ⟨(CFSG.KC.EnumSound.beq_iff _ _).1 hb, CFSG.KC.EnumSound.bIf_true hb hr⟩

theorem cTree_sound {n w : ℕ} {Y R : ℕ → ℕ} {N k : ℕ} {E EI : ℕ → ℕ} {p q : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))} {e : ℕ → Equiv.Perm (Fin n)} {x y : Equiv.Perm (Fin n)}
    (hE : ∀ j < k, PRep n w (E j) (e j)) (hEI : ∀ j < k, PRep n w (EI j) (e j)⁻¹)
    (heG : ∀ j < k, e j ∈ G) (hp : PRep n w p x) (hq : PRep n w q y)
    (hT : cTree n w (mask w) Y R N k E EI p q = true) {r : ℕ} (hr : r < N) :
    ∃ c ∈ G, PRep n w (Y r) (c * (x * y) * c⁻¹) := by
  suffices H : ∀ d r, r < N → cDep R r = d → ∃ c ∈ G, PRep n w (Y r) (c * (x * y) * c⁻¹) from
    H _ r hr rfl
  intro d
  induction d with
  | zero =>
    intro r hr hd
    rcases cRec_spec (allN_spec hT r hr) with ⟨-, h⟩ | ⟨par, lab, -, -, hpar, -⟩
    · refine ⟨1, G.one_mem, ?_⟩
      rw [one_mul, inv_one, mul_one]
      exact CFSG.KC.EnumSound.eq2_prep h hp hq
    · omega
  | succ d ih =>
    intro r hr hd
    rcases cRec_spec (allN_spec hT r hr) with ⟨h0, -⟩ | ⟨par, lab, hpN, hlab, hpar, h⟩
    · omega
    · obtain ⟨c, hc, hY⟩ := ih par hpN (by omega)
      refine ⟨e lab * c, G.mul_mem (heG lab hlab) hc, ?_⟩
      have h' := CFSG.KC.EnumSound.eq3_prep h (hE lab hlab) hY (hEI lab hlab)
      have e' : e lab * (c * (x * y) * c⁻¹) * (e lab)⁻¹ = e lab * c * (x * y) * (e lab * c)⁻¹ := by
        group
      rwa [e'] at h'

theorem foldr_cnt (p : ℕ → Bool) (l : List ℕ) (s : ℕ) :
    l.foldr (fun i s => nIf(p i, Nat.succ s, s)) s = s + (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases h : p a
    · simp [h]
    · simp [h]
      omega

theorem cntN_eq (n : ℕ) (p : ℕ → Bool) : cntN n p = {i | i < n ∧ p i = true}.ncard := by
  unfold cntN
  have h : {i | i < n ∧ p i = true} = ↑((List.range n).filter p).toFinset := by
    ext i
    simp [List.mem_filter, List.mem_range]
  rw [PK.foldN_eq, foldr_cnt, h, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (List.nodup_range.filter p)]
  exact Nat.zero_add _

theorem prep_pkP {p p' : ℕ} (h : permOK 820 10 (mask 10) (820 * 10) p p' = true) :
    PRep 820 10 p (pkP p) ∧ PRep 820 10 p' (pkP p)⁻¹ :=
  ⟨fun x => pkP_apply h x x.2, fun x => pkP_inv_apply h x x.2⟩

theorem kY_spec : G0 0 < 32 ∧ G0 1 < 4 ∧
    cTree 820 10 (mask 10) YT YR 72 4 ET ETI (QT (G0 0)) (TT (G0 1)) = true ∧
    incK 72 (fun r => bKey (GY r)) = true := by
  have h := kY
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, blt_iff, blt_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

@[expose] noncomputable def g0 : Equiv.Perm (Fin 820) := QP (G0 0) * TP (G0 1)

theorem G0P_eq (q : ℕ) (hq : q < 820) : G0P q = (g0 ⟨q, hq⟩ : ℕ) := by
  change GQ (G0 0) (GT (G0 1) q) = _
  rw [g0, Equiv.Perm.mul_apply, GT_eq kY_spec.2.1 q hq, GQ_eq kY_spec.1 _ (Fin.is_lt _), Fin.eta]

theorem g0_mem : g0 ∈ P :=
  P.mul_mem (QP_mem kY_spec.1) (TP_mem kY_spec.2.1)

theorem conj_g0
    (r : ℕ) :
    ∃ c ∈ H4, r < 72 → PRep 820 10 (YT r) (c * g0 * c⁻¹) := by
  rcases Nat.lt_or_ge r 72 with hr | hr
  · obtain ⟨c, hc, h⟩ := cTree_sound (G := H4) (e := EP) (x := QP (G0 0)) (y := TP (G0 1))
      (fun j hj => (prep_pkP (kE_spec hj).1).1) (fun j hj => (prep_pkP (kE_spec hj).1).2)
      (fun j hj => EP_mem_H4 hj) (prep_pkP (kQ_spec kY_spec.1).1).1
      (prep_pkP (kT_spec kY_spec.2.1).1).1 kY_spec.2.2.1 hr
    exact ⟨c, hc, fun _ => h⟩
  · exact ⟨1, H4.one_mem, fun h => absurd h (by omega)⟩

theorem card_cent_g0_le :
    Nat.card ↥(H4 ⊓ centralizer ({g0} : Set (Equiv.Perm (Fin 820)))) ≤ 16 := by
  choose c hc hY using conj_g0
  let z : ℕ → Equiv.Perm (Fin 820) := fun r => c r * g0 * (c r)⁻¹
  have hinj : Set.InjOn z (Set.Iio 72) := fun r hr r' hr' e =>
    inj_of_incK (F := GY) (g := z) (fun i hi q hq => hY i hi ⟨q, hq⟩) kY_spec.2.2.2 hr hr' e
  have hsub : z '' Set.Iio 72 ⊆ conjClass H4 g0 := by
    rintro _ ⟨r, -, rfl⟩
    exact ⟨c r, hc r, rfl⟩
  have h72 : 72 ≤ (conjClass H4 g0).ncard := by
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [hinj.ncard_image,← Finset.coe_range, Set.ncard_coe_finset,
      Finset.card_range] at h
  have h := ncard_conjClass_mul_card H4 g0
  rw [card_H4] at h
  by_contra hlt
  have := Nat.mul_le_mul h72 (Nat.lt_of_not_le hlt)
  omega

theorem kD_spec : (∀ i < 16, DT i < 128) ∧ incK 16 (fun i => bKey (GC (DT i))) = true ∧
    (∀ i < 16, baseEq bs (fun q => GC (DT i) (G0P q)) (fun q => G0P (GC (DT i) q)) = true) ∧
    Nat.beq (cntN 16 (fun i => rootA (GC (DT i)))) 4 = true := by
  have h := kD
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨fun i hi => blt_iff.1 (allN_spec h.1.1.1 i hi), h.1.1.2, allN_spec h.1.2, h.2⟩

theorem DE_comm {i : ℕ} (hi : i < 16) :
    CE (DT i) * g0 = g0 * CE (DT i) :=
  eq_of_baseEq (P.mul_mem (CE_mem (kD_spec.1 i hi)) g0_mem)
    (P.mul_mem g0_mem (CE_mem (kD_spec.1 i hi))) (f := fun q => GC (DT i) (G0P q))
    (f' := fun q => G0P (GC (DT i) q))
    (fun q hq => by
      rw [G0P_eq q hq, GC_eq (kD_spec.1 i hi) _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply])
    (fun q hq => by
      rw [GC_eq (kD_spec.1 i hi) q hq, G0P_eq _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply])
    (kD_spec.2.2.1 i hi)

theorem DE_injOn : Set.InjOn (fun i => CE (DT i)) (Set.Iio 16) := fun i hi j hj e =>
  inj_of_incK (F := fun i => GC (DT i)) (g := fun i => CE (DT i))
    (fun i hi q hq => GC_eq (kD_spec.1 i hi) q hq) kD_spec.2.1 hi hj e

theorem cent_g0_eq :
    (fun i => CE (DT i)) '' Set.Iio 16 =
      ((H4 ⊓ centralizer ({g0} : Set (Equiv.Perm (Fin 820))) : Subgroup _) : Set _) := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro _ ⟨i, hi, rfl⟩
    exact mem_inf.2 ⟨CE_mem_H4 (kD_spec.1 i hi), mem_centralizer_singleton_iff.2 (DE_comm hi)⟩
  · rw [DE_injOn.ncard_image,← Finset.coe_range, Set.ncard_coe_finset,
      Finset.card_range, ← Nat.card_coe_set_eq]
    exact card_cent_g0_le

@[expose] def Rt (x : Equiv.Perm (Fin 820)) : Set (Equiv.Perm (Fin 820)) :=
  {h | h ∈ H4 ∧ h * x = x * h ∧ h * h = CP 0}

theorem ncard_Rt_g0 :
    (Rt g0).ncard = 4 := by
  have h : Rt g0 = (fun i => CE (DT i)) '' {i | i < 16 ∧ rootA (GC (DT i)) = true} := by
    ext h
    constructor
    · rintro ⟨hH, hc, hs⟩
      have hm : h ∈ ((H4 ⊓ centralizer ({g0} : Set (Equiv.Perm (Fin 820))) : Subgroup _) :
          Set _) := mem_inf.2 ⟨hH, mem_centralizer_singleton_iff.2 hc⟩
      rw [← cent_g0_eq] at hm
      obtain ⟨i, hi, rfl⟩ := hm
      exact ⟨i, ⟨hi, rootA_of_sq (GC_eq (kD_spec.1 i hi)) hs⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hr⟩, rfl⟩
      exact ⟨CE_mem_H4 (kD_spec.1 i hi), DE_comm hi,
        sq_of_rootA (CE_mem (kD_spec.1 i hi)) (GC_eq (kD_spec.1 i hi)) hr⟩
  rw [h, (DE_injOn.mono fun i hi => hi.1).ncard_image, ← cntN_eq]
  exact Nat.eq_of_beq_eq_true kD_spec.2.2.2

theorem CE_conj_g0
    {c : ℕ} (hc1 : 32 ≤ c)
    (hc2 : c < 128) (hs : CE c * CE c = CP 0) : ∃ x ∈ H4, CE c = x * g0 * x⁻¹ := by
  have hk : c / 32 - 1 < 3 := by omega
  have hj : c % 32 < 32 := Nat.mod_lt c (by norm_num)
  have h := allN_spec (allN_spec kRoot (c / 32 - 1) hk) (c % 32) hj
  have e : Nat.add (Nat.mul 32 (Nat.succ (c / 32 - 1))) (c % 32) = c := by
    change 32 * (c / 32 - 1 + 1) + c % 32 = c
    omega
  rw [CFSG.KS.U43Mod.strictB_eq, e] at h
  have h := CFSG.KC.EnumSound.bIf_true (rootA_of_sq (GC_eq hc2) hs) h
  rw [CFSG.KS.U43Mod.strictB_eq, bAnd_iff, blt_iff] at h
  obtain ⟨hr, hb⟩ := h
  obtain ⟨x, hx, hY⟩ := conj_g0 (RI (Nat.add (Nat.mul 32 (c / 32 - 1)) (c % 32)))
  refine ⟨x, hx, eq_of_baseEq (CE_mem hc2)
    (P.mul_mem (P.mul_mem (H4_le_P hx) g0_mem) (P.inv_mem (H4_le_P hx))) (GC_eq hc2)
    (fun q hq => hY hr ⟨q, hq⟩) hb⟩

theorem Rt_conj
    {x : Equiv.Perm (Fin 820)}
    (hx : x ∈ H4) (y : Equiv.Perm (Fin 820)) :
    Rt (x * y * x⁻¹) = (fun h => x * h * x⁻¹) '' Rt y := by
  have hxa : x⁻¹ * CP 0 * x = CP 0 := by
    calc x⁻¹ * CP 0 * x = x⁻¹ * (CP 0 * x) := mul_assoc _ _ _
      _ = x⁻¹ * (x * CP 0) := by rw [comm_of_mem_H4 hx]
      _ = CP 0 := by group
  ext h
  constructor
  · rintro ⟨hH, hc, hs⟩
    refine ⟨x⁻¹ * h * x, ⟨H4.mul_mem (H4.mul_mem (H4.inv_mem hx) hH) hx, ?_, ?_⟩, by group⟩
    · calc x⁻¹ * h * x * y = x⁻¹ * (h * (x * y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * y * x⁻¹) * h) * x := by rw [hc]
        _ = y * (x⁻¹ * h * x) := by group
    · calc x⁻¹ * h * x * (x⁻¹ * h * x) = x⁻¹ * (h * h) * x := by group
        _ = CP 0 := by rw [hs, hxa]
  · rintro ⟨h, ⟨hH, hc, hs⟩, rfl⟩
    refine ⟨H4.mul_mem (H4.mul_mem hx hH) (H4.inv_mem hx), ?_, ?_⟩
    · calc x * h * x⁻¹ * (x * y * x⁻¹) = x * (h * y) * x⁻¹ := by group
        _ = x * (y * h) * x⁻¹ := by rw [hc]
        _ = x * y * x⁻¹ * (x * h * x⁻¹) := by group
    · have hxa' : x * CP 0 * x⁻¹ = CP 0 := by
        rw [comm_of_mem_H4 hx, mul_inv_cancel_right]
      calc x * h * x⁻¹ * (x * h * x⁻¹) = x * (h * h) * x⁻¹ := by group
        _ = CP 0 := by rw [hs, hxa']

theorem ncard_Rt_CE
    {c : ℕ} (hc1 : 32 ≤ c)
    (hc2 : c < 128) (hs : CE c * CE c = CP 0) : (Rt (CE c)).ncard = 4 := by
  obtain ⟨x, hx, e⟩ := CE_conj_g0 hc1 hc2 hs
  rw [e, Rt_conj hx, Set.ncard_image_of_injective _
    (fun a b e => mul_left_cancel (mul_right_cancel e)), ncard_Rt_g0]

end CertificateChecks.KernelU43CentPlus

end
