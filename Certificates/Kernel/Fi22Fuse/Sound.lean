module

public import Certificates.Kernel.Fi22Fuse.ChkDefs
public import Certificates.Kernel.Fi22Flag.Sound
public import Certificates.Kernel.Fi22Cent.Facts
public import CFSG.Sporadic.Fi22.Centralizer
import Certificates.Kernel.Fi22Fuse.Checks
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import CFSG.Fischer.T46Unitary

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22Fuse.c25240evAll CertificateChecks.KernelFi22Fuse.c25240evSl 10

#kon_join CertificateChecks.KernelFi22Fuse.c25240All CertificateChecks.KernelFi22Fuse.c25240Sl 128

namespace CertificateChecks.KernelFi22Fuse

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22Cent CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CertificateChecks.KernelFi22S
  CertificateChecks.KernelFi22Flag CFSG.KS.Fi22L

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


@[expose] noncomputable def fuseSpan : Subgroup J := Subgroup.closure {x | x ∈ D ∧ x ∈ slvl 0}

theorem q_mem : ∀ i < 13, c25240q i ∈ QL := by decide

theorem QL_q : ∀ q ∈ QL, ∃ i < 13, c25240q i = q := by decide

theorem eq_of_QL {g h : J} (hq : ∀ i < 13, idx 3510 g (c25240q i) = idx 3510 h (c25240q i)) :
    g = h := by
  have e : h⁻¹ * g = 1 := one_of_QL fun q hq' => by
    obtain ⟨i, hi, rfl⟩ := QL_q q hq'
    rw [idx_mul, hq i hi, idx_inv_idx]
  exact (inv_mul_eq_one.1 e).symm

theorem agE_spec {H : Nat → Nat} {m : Nat} (h : c25240agE H m = true) :
    ∀ i < 13, H (c25240q i) = c25240ev m i := fun i hi =>
  Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 h i hi)

theorem tree_mul_mem {k j : ℕ} (hk : k < 1024) (hj : j < 128) :
    treeG TS[0]! (pairG sylG) k * treeG TS[1]! (pairG sylG) j ∈ slvl 0 := by
  have hk' : k < TS[0]!.pts.size := by rw [TS_size (l := 0) rfl]; exact hk
  have hj' : j < TS[1]!.pts.size := by rw [TS_size (l := 1) rfl]; exact hj
  exact (slvl 0).mul_mem ((syl_facts.1 0 (by rw [sylBase_size]; norm_num)).treeG_mem hk')
    (levelGroup_anti (pairG sylG) (Nat.zero_le 1)
      ((syl_facts.1 1 (by rw [sylBase_size]; norm_num)).treeG_mem hj'))

theorem codes_lt : ∀ b < 10, List.getD c25240B b 0 / 128 < 1024 := by decide

theorem gA_idx {x : ℕ} (hx : x < 3510) : gA x = idx 3510 a x := by
  have e : ap orb.alpha x = gA x := by
    rw [orb_eq]
    exact (KernelFi22C.alpha_get hx).1
  rw [← e]
  exact rep_alpha x hx

theorem basis_spec {b : ℕ} (hb : b < 10) :
    ∃ x ∈ fuseSpan, ∀ y < 3510, c25240bK b y = idx 3510 x y := by
  set c := List.getD c25240B b 0 with hc
  have hk : c / 128 < 1024 := codes_lt b hb
  have hj : c % 128 < 128 := Nat.mod_lt _ (by norm_num)
  set x := treeG TS[0]! (pairG sylG) (c / 128) * treeG TS[1]! (pairG sylG) (c % 128)
  have hx : ∀ y < 3510, idx 3510 x y = gK (c / 128) (c % 128) y := leaf_idx hk hj
  have hG : ∀ y < 3510, c25240bK b y = idx 3510 x y := fun y hy => by
    unfold c25240bK
    rw [Raw.Orb.strictN_eq, hx y hy]
    rfl
  have hf : c24671flagF (c25240bK b) = true := Raw.Orb.allN_iff.1 c25240flag_ok b hb
  unfold c24671flagF at hf
  rw [Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at hf
  obtain ⟨hsq, -, hcb⟩ := hf
  have h2 : x ^ 2 = 1 := by
    rw [pow_two]
    refine one_of_QL fun q hq => ?_
    have hq' := QL_lt q hq
    have := allFix_spec hsq q hq
    unfold KernelFi22S.sq at this
    rw [Raw.Orb.strictN_eq, hG q hq', hG _ (idx_lt x hq'), ← idx_mul] at this
    exact this
  have h3 : (x * a) ^ 3 = 1 := by
    rw [pow_three']
    refine one_of_QL fun q hq => ?_
    have hq' := QL_lt q hq
    have := allFix_spec hcb q hq
    unfold cb at this
    simp only [Raw.Orb.strictN_eq] at this
    have e : ∀ y < 3510, c25240bK b (gA y) = idx 3510 (x * a) y := fun y hy => by
      rw [gA_idx hy, hG _ (idx_lt a hy)]
      exact (idx_mul x a y).symm
    rw [e q hq', e _ (idx_lt _ hq'), e _ (idx_lt _ (idx_lt _ hq')), ← idx_mul, ← idx_mul] at this
    exact this
  exact ⟨x, Subgroup.subset_closure ⟨mem_D_of_cube a_mem_D h2 h3, tree_mul_mem hk hj⟩, hG⟩

theorem ev_succ {b d : ℕ} (hb : b < 10) (hd : d < 2 ^ b) {i : ℕ} (hi : i < 13) :
    c25240ev (2 ^ b + d) i = c25240bK b (c25240ev d i) := by
  have h := c25240evAll b hb
  unfold c25240evSl at h
  exact Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 h d hd) i hi)

theorem ev_spec : ∀ m < 1024, ∃ e ∈ fuseSpan, ∀ i < 13, c25240ev m i = idx 3510 e (c25240q i) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · refine ⟨1, fuseSpan.one_mem, fun i hi => ?_⟩
      rw [idx_one]
      exact Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 c25240ev0_ok i hi)
    · set b := Nat.log 2 m
      have hb1 : 2 ^ b ≤ m := Nat.pow_log_le_self 2 hpos.ne'
      have hb2 : m < 2 ^ (b + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
      have hb : b < 10 := by
        by_contra hc
        have : 2 ^ 10 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hd : m - 2 ^ b < 2 ^ b := by rw [pow_succ] at hb2; omega
      obtain ⟨e, he, hev⟩ := ih (m - 2 ^ b) (by omega) (by omega)
      obtain ⟨x, hx, hxv⟩ := basis_spec hb
      refine ⟨x * e, fuseSpan.mul_mem hx he, fun i hi => ?_⟩
      have em : m = 2 ^ b + (m - 2 ^ b) := by omega
      rw [em, ev_succ hb hd hi, hev i hi, hxv _ (idx_lt e (QL_lt _ (q_mem i hi))), idx_mul]

theorem mem_of_inE {H : Nat → Nat} {h : J} (hH : ∀ y < 3510, H y = idx 3510 h y)
    (hE : c25240inE H = true) : h ∈ fuseSpan := by
  unfold c25240inE at hE
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at hE
  obtain ⟨hm, hag⟩ := hE
  have hm' : lk D.POS (H 0) < 1024 := by simpa [Nat.blt_eq] using hm
  obtain ⟨e, he, hev⟩ := ev_spec _ hm'
  have heq : h = e := eq_of_QL fun i hi => by
    rw [← hH _ (QL_lt _ (q_mem i hi)), agE_spec hag i hi, hev i hi]
  rw [heq]
  exact he

theorem cK_eq {u x : ℕ} (hu : u < 3510) (hx : x < 3510) : cK u x = idx 3510 (conjPt u) x := by
  have h := rep_cTab u hu x hx
  rw [CertificateChecks.KernelFi22S.orb_eq, CertificateChecks.KernelFi22Cent.cTab_eq hu hx] at h
  exact h

theorem C_lt : ∀ u ∈ c25240C, u < 3510 := by decide

theorem anyC_spec {G : Nat → Nat} {y : J} (hG : ∀ x < 3510, G x = idx 3510 y x) :
    ∀ l : List Nat, (∀ u ∈ l, u < 3510) →
      List.rec (motive := fun _ => Bool) false
        (fun u _ ih => bIf(c25240inE (c25240cj u G), true, ih)) l = true →
      ∃ c : J, c * y * c⁻¹ ∈ fuseSpan
  | [], _, h => absurd h Bool.false_ne_true
  | u :: l, hl, h => by
    change bIf(c25240inE (c25240cj u G), true, List.rec (motive := fun _ => Bool) false
      (fun u _ ih => bIf(c25240inE (c25240cj u G), true, ih)) l) = true at h
    rw [Raw.Orb.bIf_eq] at h
    by_cases hc : c25240inE (c25240cj u G) = true
    · have hu := hl u List.mem_cons_self
      set c := conjPt u
      have hcD : c ∈ D := mem_D_iff.2 ⟨u, hu, rfl⟩
      have hcc : c * c = 1 := by
        rw [← pow_two, ← orderOf_of_mem_D hcD]
        exact pow_orderOf_eq_one c
      have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
      have hH : ∀ x < 3510, c25240cj u G x = idx 3510 (c * y * c⁻¹) x := fun x hx => by
        unfold c25240cj
        rw [Raw.Orb.strictN_eq, Raw.Orb.strictN_eq, cK_eq hu hx, hG _ (idx_lt c hx),
          cK_eq hu (idx_lt y (idx_lt c hx)), hci, idx_mul, idx_mul]
      exact ⟨c, mem_of_inE hH hc⟩
    · rw [if_neg hc] at h
      exact anyC_spec hG l (fun v hv => hl v (List.mem_cons_of_mem u hv)) h

theorem exists_conj_of_mem_slvl {y : J} (hy : y ∈ slvl 0) (hy2 : y ^ 2 = 1) :
    ∃ c : J, c * y * c⁻¹ ∈ fuseSpan := by
  obtain ⟨k0, hk0, h, hh, rfl⟩ := exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hy
  obtain ⟨k1, hk1, h', hh', rfl⟩ := exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
  have hh'' : h' ∈ slvl 2 := hh'
  rw [slvl_two, Subgroup.mem_bot] at hh''
  subst hh''
  rw [mul_one] at hy2 ⊢
  rw [TS_size (l := 0) rfl] at hk0
  rw [TS_size (l := 1) rfl] at hk1
  set y := treeG TS[0]! (pairG sylG) k0 * treeG TS[1]! (pairG sylG) k1
  have hG : ∀ x < 3510, gK k0 k1 x = idx 3510 y x := fun x hx => (leaf_idx hk0 hk1 x hx).symm
  have hl : c25240F (gK k0 k1) = true := by
    have hs : k0 / 8 < 128 := by omega
    have h := c25240All (k0 / 8) hs
    unfold c25240Sl at h
    have h' := Raw.Orb.allN_iff.1 h (k0 % 8) (Nat.mod_lt _ (by norm_num))
    rw [Raw.Orb.strictB_eq] at h'
    have e : Nat.add (Nat.mul (k0 / 8) 8) (k0 % 8) = k0 := Nat.div_add_mod' k0 8
    rw [e] at h'
    exact Raw.Orb.allN_iff.1 h' k1 hk1
  unfold c25240F at hl
  rw [Raw.Orb.bIf_eq] at hl
  by_cases h1 : anyMv (KernelFi22S.sq (gK k0 k1)) = true
  · exfalso
    obtain ⟨q, hq, hne⟩ := anyMv_spec h1
    have hq' := QL_lt q hq
    apply hne
    unfold KernelFi22S.sq
    rw [Raw.Orb.strictN_eq, hG q hq', hG _ (idx_lt y hq'), ← idx_mul, ← pow_two, hy2, idx_one]
  rw [if_neg h1, Raw.Orb.bIf_eq] at hl
  by_cases h2 : allFix (gK k0 k1) = true
  · have e : y = 1 := one_of_QL fun q hq => by
      rw [← hG q (QL_lt q hq)]
      exact allFix_spec h2 q hq
    refine ⟨1, ?_⟩
    rw [e]
    simpa using fuseSpan.one_mem
  rw [if_neg h2, Raw.Orb.bIf_eq] at hl
  by_cases h3 : c25240inE (gK k0 k1) = true
  · exact ⟨1, by simpa using mem_of_inE hG h3⟩
  rw [if_neg h3] at hl
  exact anyC_spec hG c25240C C_lt hl

theorem exists_conj_mem_fuseSpan {x : J} (hx : orderOf x = 2) :
    ∃ c : J, c * x * c⁻¹ ∈ fuseSpan := by
  obtain ⟨g, hg⟩ := exists_conj_mem_slvl hx
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨c, hc⟩ := exists_conj_of_mem_slvl hg (by rw [conj_pow, hx2, mul_one, mul_inv_cancel])
  refine ⟨c * g, ?_⟩
  have e : c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ := by group
  rw [e]
  exact hc

end CertificateChecks.KernelFi22Fuse

end
