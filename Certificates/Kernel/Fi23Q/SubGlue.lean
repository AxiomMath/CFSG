module

public import Certificates.Kernel.Fi23Q.SylowGlue
public import Certificates.Kernel.Fi23Q.SubChainDefs
import CFSG.Certificates.Kernel.Fi23Q.SubChainSound
import Certificates.Kernel.Fi23Q.SubChk
import Certificates.Kernel.Fi23Q.SubChainChk

public section

namespace CertificateChecks.KernelFi23Q

open CFSG.Sporadic.Fi23 CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KS.Pc3 CFSG.KS.Fi23Q
  CFSG.Perm CFSG.KD.Fi23K
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow (pcSub pc_card_le)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Words

variable {G : Type*} [Group G]

@[expose] noncomputable def swF (m SV v i : ℕ) (acc : List ℕ) : List ℕ :=
  Bool.rec (motive := fun _ => List ℕ)
    (Bool.rec (motive := fun _ => List ℕ)
      (nwR 13 (f32 SV (m - 1 - i)) ++ (nwR 13 (f32 SV (m - 1 - i)) ++ acc))
      (nwR 13 (f32 SV (m - 1 - i)) ++ acc) (Nat.beq (dg v (m - 1 - i)) 1))
    acc (Nat.beq (dg v (m - 1 - i)) 0)

theorem swR_eq (m SV v : ℕ) :
    swR m SV v = Nat.rec (motive := fun _ => List ℕ) [] (fun i acc => swF m SV v i acc) m := rfl

theorem swF_spec (x : ℕ → G) (m SV v i : ℕ) (acc : List ℕ) (hd : dg v (m - 1 - i) < 3) :
    wd x (swF m SV v i acc) =
        wd x (nwR 13 (f32 SV (m - 1 - i))) ^ dg v (m - 1 - i) * wd x acc ∧
      ∀ c ∈ swF m SV v i acc, c ∈ nwR 13 (f32 SV (m - 1 - i)) ∨ c ∈ acc := by
  have b00 : Nat.beq 0 0 = true := rfl
  have b10 : Nat.beq 1 0 = false := rfl
  have b11 : Nat.beq 1 1 = true := rfl
  have b20 : Nat.beq 2 0 = false := rfl
  have b21 : Nat.beq 2 1 = false := rfl
  unfold swF
  obtain h | h | h : dg v (m - 1 - i) = 0 ∨ dg v (m - 1 - i) = 1 ∨ dg v (m - 1 - i) = 2 := by
    omega
  all_goals
    simp only [h, b00, b10, b11, b20, b21]
    refine ⟨by simp [wd_append, pow_two, mul_assoc], fun c hc => ?_⟩
    try simp only [List.mem_append] at hc
    tauto

theorem swR_aux (x : ℕ → G) (m SV v : ℕ) (hd : ∀ k, dg v k < 3)
    (hS : ∀ k < m, ∀ c ∈ nwR 13 (f32 SV k), c < 13) : ∀ i, i ≤ m →
    wd x (Nat.rec (motive := fun _ => List ℕ) [] (fun i acc => swF m SV v i acc) i) =
      ((List.range i).map fun j => wd x (nwR 13 (f32 SV (m - i + j))) ^ dg v (m - i + j)).prod ∧
    ∀ c ∈ Nat.rec (motive := fun _ => List ℕ) [] (fun i acc => swF m SV v i acc) i, c < 13
  | 0, _ => ⟨by simp [wd], fun c hc => absurd hc (by simp)⟩
  | i + 1, hi => by
    obtain ⟨ih1, ih2⟩ := swR_aux x m SV v hd hS i (by omega)
    obtain ⟨f1, f2⟩ := swF_spec x m SV v i
      (Nat.rec (motive := fun _ => List ℕ) [] (fun i acc => swF m SV v i acc) i) (hd _)
    refine ⟨?_, fun c hc => ?_⟩
    · change wd x (swF m SV v i _) = _
      rw [f1, ih1, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      have e0 : m - (i + 1) + 0 = m - 1 - i := by omega
      have e1 : ∀ j, m - (i + 1) + (j + 1) = m - i + j := fun j => by omega
      rw [e0]
      congr 2
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, e1]
    · rcases f2 c hc with h | h
      · exact hS _ (by omega) c h
      · exact ih2 c h

theorem swR_spec (x : ℕ → G) {m SV v : ℕ} (hd : ∀ k, dg v k < 3)
    (hS : ∀ k < m, ∀ c ∈ nwR 13 (f32 SV k), c < 13) :
    wd x (swR m SV v) = nv (fun k => wd x (nwR 13 (f32 SV k))) m v ∧
      ∀ c ∈ swR m SV v, c < 13 := by
  obtain ⟨h1, h2⟩ := swR_aux x m SV v hd hS m le_rfl
  rw [swR_eq]
  refine ⟨?_, h2⟩
  rw [h1]
  simp [nv]

theorem nv_unit9 (x : ℕ → G) {k : ℕ} (hk : k < 9) : nv x 9 (4 ^ k) = x k := by
  unfold nv
  rw [prod_range_single _ 9 hk fun m _ hmk => by rw [dg_unit, if_neg hmk, pow_zero]]
  rw [dg_unit, if_pos rfl, pow_one]

theorem nv_zero9 (x : ℕ → G) : nv x 9 0 = 1 := by
  unfold nv
  apply List.prod_eq_one
  intro g hg
  simp only [List.mem_map, List.mem_range] at hg
  obtain ⟨m, -, rfl⟩ := hg
  rw [dg_eq, Nat.zero_div, Nat.zero_mod, pow_zero]

theorem nv_congr9 {x y : ℕ → G} (h : ∀ k < 9, x k = y k) (v : ℕ) : nv x 9 v = nv y 9 v := by
  unfold nv
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [h k (List.mem_range.1 hk)]

end Words

theorem vecOK9_13 {u : ℕ} (h : vecOK 9 u = true) : vecOK 13 u = true := by
  obtain ⟨h1, h2⟩ := band_true h
  unfold vecOK
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true]
  refine ⟨?_, h2⟩
  rw [Nat.blt_eq] at h1 ⊢
  exact lt_of_lt_of_le h1 (by decide)

theorem vecOK9_dg {u : ℕ} (h : vecOK 9 u = true) (k : ℕ) : dg u k < 3 := vecOK_dg (vecOK9_13 h) k

theorem unit9_ok : ∀ k < 9, vecOK 9 (4 ^ k) = true := by decide +kernel

@[expose] noncomputable def sE (k : ℕ) : CFSG.Sporadic.Fi23.J :=
  nv aE 13 (f32 CFSG.KD.Fi23Q.SubV k)

theorem relS_parts : pcDataOK 9 CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ = true ∧
    relW CFSG.KD.Fi23Q.H 9 CFSG.KD.Fi23Q.SubV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ = true := by
  have h := CFSG.KD.Fi23Q.relSK_ok
  unfold CFSG.KD.Fi23Q.relSK CFSG.KD.Fi23Q.relSW at h
  rwa [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h

theorem sv_ok : ∀ k < 9, vecOK 13 (f32 CFSG.KD.Fi23Q.SubV k) = true := by
  have h := relS_parts.2
  unfold relW at h
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff] at h
  exact h.1

theorem sv_letters : ∀ k < 9, ∀ c ∈ nwR 13 (f32 CFSG.KD.Fi23Q.SubV k), c < 13 :=
  fun k hk => (nwR_spec (fun _ => (1 : Multiplicative ℤ)) (vecOK_dg (sv_ok k hk))).2

theorem swS_spec {v : ℕ} (hv : vecOK 9 v = true) :
    wd aE (swR 9 CFSG.KD.Fi23Q.SubV v) = nv sE 9 v ∧
      ∀ c ∈ swR 9 CFSG.KD.Fi23Q.SubV v, c < 13 := by
  obtain ⟨h1, h2⟩ := swR_spec aE (vecOK9_dg hv) sv_letters
  refine ⟨h1.trans (nv_congr9 (fun k hk => ?_) v), h2⟩
  exact (nwR_spec aE (vecOK_dg (sv_ok k hk))).1

theorem pcRelS :
    PcRel sE 9 CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ := by
  obtain ⟨hd, hr⟩ := relS_parts
  have hE := eqH_rep aE aE_acts
  unfold relW at hr
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff, List.append_eq] at hr
  unfold pcDataOK at hd
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff,
    CFSG.KS.PK.strictB_eq] at hd
  obtain ⟨-, hc, hj⟩ := hr
  constructor
  · intro k hk
    obtain ⟨W1, W2⟩ := swS_spec (hd.2 k hk).1
    obtain ⟨S1, S2⟩ := nwR_spec aE (vecOK_dg (sv_ok k hk))
    have e := eqH_wd hE (allLt_append S2 (allLt_append S2 S2)) W2 (hc k hk)
    rw [wd_append, wd_append, S1, W1] at e
    rw [← e, sE, pow_succ, pow_two, mul_assoc]
  · intro i j hij hj9
    have hi : i < 9 := by omega
    have hcj := (hd.2 i hi).2.2 j hj9
    have hrel := hj i hi j hj9
    simp only [CFSG.KS.PK.bIf_eq, Nat.blt_eq, hij, ↓reduceIte, CFSG.KS.PK.strictB_eq,
      CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, cj_index] at hcj hrel
    obtain ⟨C1, C2⟩ := swS_spec hcj.1
    obtain ⟨I1, I2⟩ := nwR_spec aE (vecOK_dg (sv_ok i hi))
    obtain ⟨J1, J2⟩ := nwR_spec aE (vecOK_dg (sv_ok j hj9))
    have e := eqH_wd hE (allLt_append J2 I2) (allLt_append I2 C2) hrel
    rw [wd_append, wd_append, I1, J1, C1] at e
    change sE j * sE i = sE i * nv sE 9 _ at e
    rw [mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]

noncomputable abbrev SubS : Subgroup CFSG.Sporadic.Fi23.J := Subgroup.closure (sE '' Set.Iio 9)

theorem nvS_mem (v : ℕ) : nv sE 9 v ∈ SubS := by
  unfold nv
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  have hk' : sE k ∈ sE '' Set.Iio 9 := ⟨k, List.mem_range.1 hk, rfl⟩
  exact Subgroup.pow_mem _ (Subgroup.subset_closure hk') _

theorem nfS
    {y : CFSG.Sporadic.Fi23.J} (hy : y ∈ SubS) :
    ∃ v, vecOK 9 v = true ∧ nv sE 9 v = y := by
  have hd := relS_parts.1
  have hP := pcRelS
  have hmul : ∀ a b : J, (∃ u, vecOK 9 u = true ∧ nv sE 9 u = a) →
      (∃ u, vecOK 9 u = true ∧ nv sE 9 u = b) → ∃ u, vecOK 9 u = true ∧ nv sE 9 u = a * b := by
    rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨_, (mulV_sound hd hP hu hv).1, (mulV_sound hd hP hu hv).2⟩
  have h0 : ∃ u, vecOK 9 u = true ∧ nv sE 9 u = 1 := ⟨0, by decide, nv_zero9 sE⟩
  have hpow : ∀ a : J, (∃ u, vecOK 9 u = true ∧ nv sE 9 u = a) →
      ∀ n : ℕ, ∃ u, vecOK 9 u = true ∧ nv sE 9 u = a ^ n := by
    intro a ha n
    induction n with
    | zero => simpa using h0
    | succ n ih => simpa [pow_succ] using hmul _ _ ih ha
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, hk, rfl⟩ := hg
    exact ⟨4 ^ k, unit9_ok k hk, nv_unit9 sE hk⟩
  | one => exact h0
  | mul a b _ _ ha hb => exact hmul a b ha hb
  | inv a _ ha =>
    obtain ⟨w, hw, he⟩ := hpow a ha (orderOf a - 1)
    refine ⟨w, hw, he.trans ?_⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]

theorem nvS_mem_tail {w i : ℕ} (hw : ∀ m ≤ i, dg w m = 0) :
    nv sE 9 w ∈ Subgroup.closure (sE '' {k | i + 1 ≤ k ∧ k < 9}) := by
  unfold nv
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  have hk' := List.mem_range.1 hk
  by_cases hki : k ≤ i
  · rw [hw k hki, pow_zero]
    exact Subgroup.one_mem _
  · have hm : sE k ∈ sE '' {k | i + 1 ≤ k ∧ k < 9} := ⟨k, ⟨by omega, hk'⟩, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.subset_closure hm) _

@[expose] noncomputable def sa (i : Fin 9) : SubS :=
  ⟨(sE i)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, i.isLt, rfl⟩)⟩

theorem mem_pcSubS (j : ℕ) (y : SubS)
    (hy : (y : J) ∈ Subgroup.closure (sE '' {k | j ≤ k ∧ k < 9})) : y ∈ pcSub sa j := by
  have hle : Subgroup.closure (sE '' {k | j ≤ k ∧ k < 9}) ≤
      (pcSub sa j).map SubS.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, ⟨hjk, hk⟩, rfl⟩
    refine ⟨(sa ⟨k, hk⟩)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨k, hk⟩, hjk, rfl⟩), ?_⟩
    simp [sa]
  obtain ⟨z, hz, e⟩ := Subgroup.mem_map.1 (hle hy)
  have hzy : z = y := Subtype.ext e
  rwa [← hzy]

theorem sa_gen : Subgroup.closure (Set.range sa) = ⊤ := by
  rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage, Subgroup.closure_le]
  rintro y ⟨k, hk, e⟩
  have hy : y = (sa ⟨k, hk⟩)⁻¹ := Subtype.ext (by simp [sa, e])
  rw [hy]
  exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, rfl⟩)

theorem card_S_le :
    Nat.card SubS ≤ 3 ^ 9 := by
  have hd := relS_parts.1
  have hP := pcRelS
  unfold pcDataOK at hd
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff,
    CFSG.KS.PK.strictB_eq] at hd
  refine (pc_card_le (p := 3) (by norm_num) sa sa_gen (fun i => ?_) (fun i j hij => ?_)).2
  · apply mem_pcSubS
    have hw := (hd.2 i i.isLt).2.1
    rw [lowV_eq] at hw
    have hw' := Nat.eq_of_beq_eq_true hw
    have e : (((sa i) ^ 3 : SubS) : J) = (nv sE 9 (f32 CFSG.KD.Fi23Q.SubPW i))⁻¹ := by
      rw [SubgroupClass.coe_pow, sa, inv_pow, hP.cube i i.isLt]
    rw [e]
    exact Subgroup.inv_mem _ (nvS_mem_tail fun m hm => dg_zero_of_mod hw' (by omega))
  · apply mem_pcSubS
    have hj9 := j.isLt
    have hij' : i.val < j.val := hij
    have hcj := (hd.2 i i.isLt).2.2 j hj9
    simp only [CFSG.KS.PK.bIf_eq, Nat.blt_eq, hij', ↓reduceIte, CFSG.KS.PK.strictB_eq,
      CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, cj_index] at hcj
    have hc := Nat.eq_of_beq_eq_true hcj.2
    have h4 : Nat.shiftLeft 1 (Nat.shiftLeft j.val 1) = 4 ^ j.val := by
      change 1 <<< (j.val <<< 1) = _
      rw [Nat.shiftLeft_eq 1, one_mul, pow4]
    rw [lowV_eq, h4] at hc
    have hc' : f32 CFSG.KD.Fi23Q.SubCJ (16 * i + j) % 4 ^ j.val = 0 := by
      rw [← Nat.mod_mod_of_dvd _ (pow_dvd_pow 4 (Nat.le_succ j.val)), hc, Nat.mod_self]
    have e : ((sa i * sa j * (sa i)⁻¹ : SubS) : J) =
        (nv sE 9 (f32 CFSG.KD.Fi23Q.SubCJ (16 * i + j)))⁻¹ := by
      rw [← hP.conj i j hij' hj9]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, sa]
      group
    rw [e]
    exact Subgroup.inv_mem _ (nvS_mem_tail fun m hm => dg_zero_of_mod hc' (by omega))

theorem imgS_eq :
    ∀ v, vecOK 9 v = true → ∀ x < 31671, CFSG.KD.Fi23Q.imgS v x = idx 31671 (nv sE 9 v) x := by
  intro v hv x hx
  obtain ⟨W1, W2⟩ := swS_spec hv
  unfold CFSG.KD.Fi23Q.imgS
  rw [← W1]
  exact wvH_eq aE aE_acts W2 hx

@[expose] noncomputable def chainSE : List (ℕ × List CFSG.Sporadic.Fi23.J) :=
  CFSG.KD.Fi23Q.chainSL.map fun l => (l.1, l.2.map (nv sE 9))

theorem le_card_S :
    3 ^ 9 ≤ Nat.card SubS := by
  have hk : chainG CFSG.KD.Fi23Q.imgS (vecOK 9) CFSG.KD.Fi23Q.chainSL = true :=
    CFSG.KD.Fi23Q.chainSK_ok
  have hC := (chainG_of (act := idx 31671) imgS_eq CFSG.KD.Fi23Q.chainSL hk).1
  have hN := prs_nodup (fun g h x => idx_mul g h x) (fun x => idx_one x) _ hC
  have hlen : (prs (chainSE.map Prod.snd)).length = 3 ^ 9 := by
    rw [length_prs, chainSE, List.map_map, List.map_map]
    simp only [Function.comp_def, List.length_map]
    decide +kernel
  rw [← hlen]
  refine length_le_card _ hN (prs_mem _ _ ?_)
  intro L hL x hx
  rw [chainSE, List.map_map, List.mem_map] at hL
  obtain ⟨l, -, rfl⟩ := hL
  simp only [Function.comp_apply] at hx
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
  exact nvS_mem v

theorem card_S :
    Nat.card SubS = 3 ^ 9 :=
  le_antisymm card_S_le le_card_S

theorem sE_comm
    {k : ℕ} (hk : k < 9) :
    sE k * conjPt 770 = conjPt 770 * sE k := by
  have hf := CFSG.KD.Fi23Q.fixSK_ok
  unfold CFSG.KD.Fi23Q.fixSK fixW at hf
  rw [CFSG.KS.PK.allN_iff] at hf
  have h1 := Nat.eq_of_beq_eq_true (hf k hk)
  obtain ⟨S1, S2⟩ := nwR_spec aE (vecOK_dg (sv_ok k hk))
  rw [wvH_eq aE aE_acts S2 (by norm_num), S1, idx_of_lt _ (by norm_num)] at h1
  have hfx : sE k • (⟨770, by norm_num⟩ : Fin 31671) = ⟨770, by norm_num⟩ := Fin.ext h1
  have hc : sE k * conjPt 770 * (sE k)⁻¹ = conjPt 770 :=
    (smul_eq_iff _ ⟨770, by norm_num⟩ ⟨770, by norm_num⟩).1 hfx
  calc sE k * conjPt 770 = sE k * conjPt 770 * (sE k)⁻¹ * sE k := by group
    _ = conjPt 770 * sE k := by rw [hc]

theorem S_le_centralizer :
    SubS ≤ Subgroup.centralizer {conjPt 770} := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have e := sE_comm hk
  first
    | exact Subgroup.mem_centralizer_singleton_iff.2 e
    | exact Subgroup.mem_centralizer_singleton_iff.2 e.symm

end CertificateChecks.KernelFi23Q

end
