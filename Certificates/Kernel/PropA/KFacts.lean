module

public import Certificates.Kernel.PropA.JFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb
  CFSG.KS.PRec CFSG.KS.PMem CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA
open scoped commutatorElement

theorem pa450010_cl_le_K (b : Bool) (kS : ℕ) (ws : List (List Int)) :
    pa450010cl b kS ws ≤ K28 b :=
  (closure_le _).2 fun _ ⟨_, _, e⟩ => e ▸ pa450010wv_mem b kS _

theorem pa450010_J_le_Kx (b : Bool) :
    pa450010Jg ≤ K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) :=
  pa450010_J_le_E.trans (inf_le_inf_right _ (D28_le_K28 b))

theorem pa450010_K_of {b : Bool} {k cnt kY cntY : ℕ}
    {G GI T PL POS SRT SRI GY GIY TY PLY POSY SRTY SRIY PKJ PY Pc Py : ℕ → ℕ}
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 960 k G GI cnt T PL 4
      (pa450010S b) (pa450010SI b) pa450010wCKX = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) false G GI k cnt T PL POS SRT SRI 0 960 = true)
    (hc : centK 28 5 (mask 5) (28 * 5) k G pa450010XD.R = true)
    (hKJ : conjInK 28 5 (mask 5) pa450010J.cnt pa450010J.T PKJ G GI pa450010J.G 5 2 = true)
    (hdY : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 8 kY GY GIY cntY TY PLY 4
      (pa450010S b) (pa450010SI b) pa450010wY = true)
    (hslY : penumSlK 28 5 (mask 5) (28 * 5) false GY GIY kY cntY TY PLY POSY SRTY SRIY 0 8 =
      true)
    (hcY : bAnd(centK 28 5 (mask 5) (28 * 5) kY GY (pa450010J.G 0), bAnd(centK 28 5 (mask 5)
      (28 * 5) kY GY (pa450010J.G 1), centK 28 5 (mask 5) (28 * 5) kY GY pa450010XD.R)) = true)
    (hfilt : filtInK 28 5 (mask 5) cnt T 2 pa450010J.G cntY TY PY = true)
    (hG3 : commToK 28 5 (mask 5) cnt T Pc cntY TY Py pa450010XD.R = true) :
    K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) = pa450010cl b 4 pa450010wCKX ∧
    (pa450010Jg.subgroupOf (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))))).Normal ∧
    centralizer (pa450010Jg : Set (Perm (Fin 28))) ⊓
      (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))) = pa450010cl b 4 pa450010wY ∧
    Nat.card (pa450010cl b 4 pa450010wY) = 8 ∧
    ∃ c ∈ K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))),
      ∃ y ∈ centralizer (pa450010Jg : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))),
        c * y * c⁻¹ * y⁻¹ = pa450010x := by
  obtain ⟨xJ, hxJ, -, hmemJ, -, -, hgJ, -⟩ := pa450010_J_rec
  obtain ⟨xK, hxK, -, hmemK, hcardK, hk, hg, hgi⟩ := pa450010_rec (by norm_num) hd hsl
  obtain ⟨xY, hxY, -, hmemY, hcardY, hkY, hgY, -⟩ := pa450010_rec (by norm_num) hdY hslY
  have hk5 : k = 5 := hk
  subst hk5
  simp only [bAnd_eq, Bool.and_eq_true] at hcY
  obtain ⟨hcY0, hcY1, hcYx⟩ := hcY
  have hKeq : K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) =
      pa450010cl b 4 pa450010wCKX := by
    have hle : pa450010cl b 4 pa450010wCKX ≤
        K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) :=
      le_inf (pa450010_cl_le_K b 4 _) (pa450010_cl_le_cent hk hg hc)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [pa450010_card_Kx, hcardK])).symm
  have hJK := pa450010_J_le_Kx b
  have hYle : pa450010cl b 4 pa450010wY ≤ centralizer (pa450010Jg : Set (Perm (Fin 28))) ⊓
      (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))) := by
    refine le_inf ?_ (le_inf (pa450010_cl_le_K b 4 _) (pa450010_cl_le_cent hkY hgY hcYx))
    rw [Subgroup.le_centralizer_iff, pa450010_Jg_eq, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj2 : j < 2 := hj
    have hcl : pa450010cl b 4 pa450010wY ≤ centralizer {pa450010j j} := by
      have h := closure_le_centralizer (by norm_num) hgY (hgJ j hj2)
        (by interval_cases j; exacts [hcY0, hcY1])
      rw [hkY] at h
      exact h
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.1 (hcl hh)
  have hYeq : centralizer (pa450010Jg : Set (Perm (Fin 28))) ⊓
      (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))) = pa450010cl b 4 pa450010wY := by
    refine le_antisymm ?_ hYle
    rintro y ⟨hyJ, hyK⟩
    rw [hKeq] at hyK
    obtain ⟨q, hq, rfl⟩ := (hmemK _).1 hyK
    obtain ⟨q', hq', e⟩ := filtInK_spec (by norm_num) (by norm_num) hxK hxY hgJ hfilt q hq
      fun j hj => (mem_centralizer_iff.1 hyJ _ (pa450010_j_mem hj)).symm
    exact (hmemY _).2 ⟨q', hq', e⟩
  refine ⟨hKeq, ?_, hYeq, hcardY, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJK, hKeq]
    refine pa450010_le_normalizer ?_
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact conjInK_spec (by norm_num) hxJ hmemJ hg hgi hgJ hKJ i hi j hj
  · obtain ⟨p, hp, q, hq, e⟩ := commToK_spec (by norm_num) hxK hxY pa450010_prepX hG3
    refine ⟨xK p, by rw [hKeq]; exact (hmemK _).2 ⟨p, hp, rfl⟩, xY q,
      by rw [hYeq]; exact (hmemY _).2 ⟨q, hq, rfl⟩, ?_⟩
    rw [← commutatorElement_def]
    exact pa450010_comm_of e

theorem pa450010_K_facts (b : Bool) :
    K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) = pa450010cl b 4 pa450010wCKX ∧
    (pa450010Jg.subgroupOf (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))))).Normal ∧
    centralizer (pa450010Jg : Set (Perm (Fin 28))) ⊓
      (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))) = pa450010cl b 4 pa450010wY ∧
    Nat.card (pa450010cl b 4 pa450010wY) = 8 ∧
    ∃ c ∈ K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))),
      ∃ y ∈ centralizer (pa450010Jg : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))),
        c * y * c⁻¹ * y⁻¹ = pa450010x := by
  cases b
  · exact pa450010_K_of pa450010_CKX1_hd pa450010_CKX1_sl pa450010_CKX1_cent pa450010_KJ1
      pa450010_Y1_hd pa450010_Y1_sl pa450010_Y1_cent pa450010_Y1_filt pa450010_G3_1
  · exact pa450010_K_of pa450010_CKX2_hd pa450010_CKX2_sl pa450010_CKX2_cent pa450010_KJ2
      pa450010_Y2_hd pa450010_Y2_sl pa450010_Y2_cent pa450010_Y2_filt pa450010_G3_2

theorem pa450010_J_normal (b : Bool) :
    ((jOf D28 pa450010x).subgroupOf
      (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))))).Normal := by
  rw [pa450010_jOf_eq]
  exact (pa450010_K_facts b).2.1

theorem pa450010_card_Y (b : Bool) :
    Nat.card ↥(centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) ⊓
      (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))))) = 8 := by
  rw [pa450010_jOf_eq, (pa450010_K_facts b).2.2.1]
  exact (pa450010_K_facts b).2.2.2.1

theorem pa450010_G3 (b : Bool) :
    ∃ c ∈ K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))),
      ∃ y ∈ centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))),
        c * y * c⁻¹ * y⁻¹ = pa450010x := by
  rw [pa450010_jOf_eq]
  exact (pa450010_K_facts b).2.2.2.2

theorem pa450010_G1_of {b : Bool} {i R N k cnt : ℕ}
    {G GI T PL POS SRT SRI P : ℕ → ℕ}
    (hr : wordEqK 28 5 (mask 5) (pidn 28 5) (pa450010S b) (pa450010SI b) 4
      (pa450010wReps.getD i []) R = true)
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) R N k G GI cnt T PL 4 (pa450010S b)
      (pa450010SI b) pa450010wK = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) true G GI k cnt T PL POS SRT SRI 0 N = true)
    (h : notCentK 28 5 (mask 5) (28 * 5) cnt T P pa450010XD.R 2 pa450010J.G = true) :
    ∃ c ∈ K28 b, c * pa450010rep b i * c⁻¹ ∈ centralizer ({pa450010x} : Set (Perm (Fin 28))) ∧
      c * pa450010rep b i * c⁻¹ ∉ centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) := by
  obtain ⟨-, -, -, -, -, -, hgJ, -⟩ := pa450010_J_rec
  obtain ⟨c, hc, -, -, hcls⟩ := pa450010_conj (by norm_num) (pa450010_root (by norm_num) hr) hd
    hsl
  rw [pa450010_clK] at hcls
  obtain ⟨p, hp, hpx, hpn⟩ := notCentK_spec (by norm_num) (by norm_num) hc pa450010_prepX hgJ h
  obtain ⟨g, hg, e⟩ := (hcls _).2 ⟨p, hp, rfl⟩
  unfold pa450010rep
  refine ⟨g, hg, ?_, ?_⟩
  · rw [e]
    exact mem_centralizer_singleton_iff.2 hpx
  · rw [e, pa450010_jOf_eq]
    intro hin
    exact hpn fun j hj => (mem_centralizer_iff.1 hin _ (pa450010_j_mem hj)).symm

theorem pa450010_G1 (b : Bool) : ∀ w ∈ K28 b, orderOf w = 2 →
    w ≠ pT → ∃ c ∈ K28 b, c * w * c⁻¹ ∈ centralizer ({pa450010x} : Set (Perm (Fin 28))) ∧
      c * w * c⁻¹ ∉ centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) := by
  apply pa450010_G1_red b
  intro i hi hsq
  have hGG := pG_mul_self true
  simp only [if_true] at hGG
  obtain ⟨-, -, r4, r5⟩ := pa450010_rep_eq true
  cases b
  · interval_cases i
    · exact pa450010_G1_of pa450010_C10_root pa450010_C10_hd pa450010_C10_sl pa450010_G1_10
    · exact pa450010_G1_of pa450010_C11_root pa450010_C11_hd pa450010_C11_sl pa450010_G1_11
    · exact pa450010_G1_of pa450010_C12_root pa450010_C12_hd pa450010_C12_sl pa450010_G1_12
    · exact pa450010_G1_of pa450010_C13_root pa450010_C13_hd pa450010_C13_sl pa450010_G1_13
    · exact pa450010_G1_of pa450010_C14_root pa450010_C14_hd pa450010_C14_sl pa450010_G1_14
    · exact pa450010_G1_of pa450010_C15_root pa450010_C15_hd pa450010_C15_sl pa450010_G1_15
  · interval_cases i
    · exact pa450010_G1_of pa450010_C20_root pa450010_C20_hd pa450010_C20_sl pa450010_G1_20
    · exact pa450010_G1_of pa450010_C21_root pa450010_C21_hd pa450010_C21_sl pa450010_G1_21
    · exact pa450010_G1_of pa450010_C22_root pa450010_C22_hd pa450010_C22_sl pa450010_G1_22
    · exact pa450010_G1_of pa450010_C23_root pa450010_C23_hd pa450010_C23_sl pa450010_G1_23
    · rw [r4, hGG] at hsq
      exact absurd hsq pa450010_pT_ne_one
    · rw [r5] at hsq
      have e4 : pG true * pT * (pG true * pT) = pG true * pG true * (pT * pT) := by
        rw [mul_assoc, ← mul_assoc pT, ← pG_comm_pT true]
        group
      rw [e4, hGG, pT_mul_self, mul_one] at hsq
      exact absurd hsq pa450010_pT_ne_one

theorem pa450010_conj_R {b : Bool} {r h y : Perm (Fin 28)} {H : Subgroup (Perm (Fin 28))}
    (hH : H ≤ K28 b ⊓ centralizer ({r} : Set (Perm (Fin 28)))) (hperf : ⁅H, H⁆ = H)
    (hc : Nat.card H = 60) (hh : h ∈ K28 b) (e : h * r * h⁻¹ = y) :
    ∃ R : Subgroup (Perm (Fin 28)), R ≤ K28 b ⊓ centralizer ({y} : Set (Perm (Fin 28))) ∧
      ⁅R, R⁆ = R ∧ 60 ≤ Nat.card R := by
  refine ⟨H.map (MulAut.conj h).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hgK : g ∈ K28 b := (Subgroup.mem_inf.1 (hH hg)).1
    have hgc := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hH hg)).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.mem_inf.2 ⟨(K28 b).mul_mem ((K28 b).mul_mem hh hgK) ((K28 b).inv_mem hh), ?_⟩
    rw [mem_centralizer_singleton_iff, ← e]
    calc h * g * h⁻¹ * (h * r * h⁻¹) = h * (g * r) * h⁻¹ := by group
      _ = h * (r * g) * h⁻¹ := by rw [hgc]
      _ = h * r * h⁻¹ * (h * g * h⁻¹) := by group
  · rw [← Subgroup.map_commutator, hperf]
  · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hc]

theorem pa450010_le_cent_pT {b : Bool} {r : Perm (Fin 28)} {H : Subgroup (Perm (Fin 28))}
    (hH : H ≤ K28 b ⊓ centralizer ({r} : Set (Perm (Fin 28)))) :
    H ≤ K28 b ⊓ centralizer ({r * pT} : Set (Perm (Fin 28))) := by
  intro g hg
  have hgK : g ∈ K28 b := (Subgroup.mem_inf.1 (hH hg)).1
  have hgc := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hH hg)).2
  refine Subgroup.mem_inf.2 ⟨hgK, mem_centralizer_singleton_iff.2 ?_⟩
  rw [← mul_assoc, hgc, mul_assoc, pT_commute_of_mem_K28 b g hgK, mul_assoc]

theorem pa450010_G2 (b : Bool) : ∀ x' ∈ K28 b, orderOf x' = 2 →
    Nat.card ↥(K28 b ⊓ centralizer ({x'} : Set (Perm (Fin 28)))) ∣ 960 →
    ∃ R : Subgroup (Perm (Fin 28)), R ≤ K28 b ⊓ centralizer ({x'} : Set (Perm (Fin 28))) ∧
      ⁅R, R⁆ = R ∧ 60 ≤ Nat.card R := by
  intro y hy h2 hd
  obtain ⟨h, hh, hcase⟩ := pa450010_G2_red b hy h2 hd
  have hJ := pa450010_J_le_Kx b
  have hJc : Nat.card pa450010Jg = 60 := pa450010_J_rec.choose_spec.2.2.2.1
  obtain ⟨hRp, hRc, hRle⟩ := pa450010_R_facts
  rcases hcase with e | e | ⟨rfl, e | e⟩
  · exact pa450010_conj_R hJ pa450010_J_perf hJc hh e
  · exact pa450010_conj_R (pa450010_le_cent_pT hJ) pa450010_J_perf hJc hh e
  · exact pa450010_conj_R hRle hRp hRc hh e
  · exact pa450010_conj_R (pa450010_le_cent_pT hRle) hRp hRc hh e

end CertificateChecks.KernelPropA

end
