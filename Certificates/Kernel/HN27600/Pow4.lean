module

public import Certificates.Kernel.HN25550.Sign
public import Certificates.Kernel.HN27600.Checks
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.PNode4Sound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHN27600

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PNode CFSG.KS.PNode4
open CFSG.KD.HN25550 CFSG.KD.HN27600 CFSG.Sporadic.HNOddCore CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CertificateChecks.KernelHN25550
open CertificateChecks.KernelSpor CFSG.Sporadic.HNSchreier CFSG.ONSchreier CFSG.ONSchreier.Native
open CFSG.KS.WordRegs CFSG.KC.HNMult

theorem pgroup_of_pow8 {G : Type*} [Group G] {g : G} (h : g ^ 8 = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have h1 : orderOf g ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one (by norm_num [h])
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem sq_eq_of_ker_gen {G : Type*} [Group G] {a b t : G} (ht : t ^ 2 = 1)
    (hc : a * t = t * a) (hk : a⁻¹ * b = 1 ∨ a⁻¹ * b = t) : b ^ 2 = a ^ 2 := by
  rcases hk with h | h
  · rw [inv_mul_eq_one] at h
    rw [h]
  · obtain rfl : b = a * t := by rw [← h, mul_inv_cancel_left]
    have hcomm : Commute a t := hc
    rw [hcomm.mul_pow, ht, mul_one]

theorem tab_pt {P : ℕ} {σ : Equiv.Perm (Fin 1100)} (hrep : TabRep (unpack 1100 11 P) σ)
    (y : Fin 1100) : pg 11 (mask 11) P y = (σ y : ℕ) := by
  have h1 := hrep.apply y
  rw [HN2092.unpack_get' y.2] at h1
  exact h1

theorem tab_pow4_fix {P : ℕ} {σ : Equiv.Perm (Fin 1100)} (hrep : TabRep (unpack 1100 11 P) σ)
    (h4 : σ ^ 4 = 1) {x : ℕ} (hx : x < 1100) :
    pg 11 (mask 11) P (pg 11 (mask 11) P (pg 11 (mask 11) P (pg 11 (mask 11) P x))) = x := by
  have hx' : x = ((⟨x, hx⟩ : Fin 1100) : ℕ) := rfl
  rw [hx', tab_pt hrep, tab_pt hrep, tab_pt hrep, tab_pt hrep]
  have e : σ ^ 4 = σ * (σ * (σ * σ)) := by
    rw [pow_succ, pow_succ, pow_succ, pow_one, mul_assoc, mul_assoc]
  have h := congrArg (fun τ : Equiv.Perm (Fin 1100) => τ ⟨x, hx⟩) h4
  simp only [e, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h
  rw [h]

theorem lenL_len {α : Type} (l : List α) : CFSG.KC.Ord.lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem node4_ok {i : ℕ} (hi : i < 1024) :
    ∃ nw, node4K 1100 11 (mask 11) 1024 EP.T EP.PL PP SQ4 i nw = true := by
  obtain ⟨ha1, ha2⟩ := (by simpa only [bAnd_iff] using nodesA_ok :
    Nat.beq (CFSG.KC.Ord.lenL NWA) 512 = true ∧
      nodes4K 1100 11 (mask 11) 1024 EP.T EP.PL PP SQ4 NWA 0 = true)
  obtain ⟨hb1, hb2⟩ := (by simpa only [bAnd_iff] using nodesB_ok :
    Nat.beq (CFSG.KC.Ord.lenL NWB) 512 = true ∧
      nodes4K 1100 11 (mask 11) 1024 EP.T EP.PL PP SQ4 NWB 512 = true)
  have la : NWA.length = 512 := by
    have := Nat.eq_of_beq_eq_true ha1
    rwa [lenL_len] at this
  have lb : NWB.length = 512 := by
    have := Nat.eq_of_beq_eq_true hb1
    rwa [lenL_len] at this
  by_cases h : i < 512
  · have := nodes4K_spec NWA 0 ha2 i (by omega)
    rw [Nat.zero_add] at this
    exact ⟨_, this⟩
  · have := nodes4K_spec NWB 512 hb2 (i - 512) (by omega)
    rw [show 512 + (i - 512) = i by omega] at this
    exact ⟨_, this⟩

theorem canon_T {i : ℕ} (hi : i < 1024) :
    canonK 1100 11 (mask 11) (1100 * 11) (EP.T i) = true := by
  have h := ptP i (by rw [cnt_eq]; exact hi)
  unfold penumPtK at h
  rw [strictB_app] at h
  exact ((bAnd_iff _ _).1 h).1

section Glue

theorem conj_into8 {t g : C6} (ht : t ^ 2 = 1) (hg4 : g ^ 4 = t) :
    ∃ c : C6, phi6 (c * g * c⁻¹) ∈ Hs := by
  let σ : phi6.range := ⟨phi6 g, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩
  have e8 : g ^ 8 = (g ^ 4) ^ 2 := by rw [← pow_mul]
  have hσ : σ ^ 8 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, e8, hg4, ht, map_one])
  obtain ⟨y, hy⟩ := CFSG.EvenSporadicStandard.TwoHS.exists_conj_mem_of_dvd_card _ dvd_H
    (pgroup_of_pow8 hσ)
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 y.2
  refine ⟨c, ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hy
  rw [map_mul, map_mul, map_inv, hc]
  exact hy

theorem node_sq_one {j : ℕ} (hj : j < 1024) (hjS : j = 0 ∨ j ∈ SQ4) : nodeEl j ^ 2 = 1 := by
  rcases hjS with rfl | hjS
  · rw [nodeEl_zero, one_pow]
  · exact sq_of_relW hj (List.all_eq_true.1 rel_ok _ (sqPathsK_spec SQ4 REL4 sq_ok j hjS))

theorem pow4_contra (t : C6) (htJ : (t : JH) = aJ) (ht1 : phi6 t = 1)
    (hker : ∀ k ∈ phi6.ker, k = 1 ∨ k = t) (y : C6) (hyN : y ∈ Dsub.comap phi6)
    (hy4 : y ^ 4 = t) : False := by
  have ht2 := sq_of htJ
  obtain ⟨c, hzH⟩ := conj_into8 ht2 hy4
  obtain ⟨i, hi, hphi⟩ := exists_node hzH
  have hzN : phi6 (nodeEl i) ∈ Dsub := by
    rw [← hphi]
    exact (conj_mem_iff c y).2 (Subgroup.mem_comap.1 hyN)
  have hev : parK PP (pathK EP.PL i i) ≠ 1 := by
    rw [(node_mem_iff i).1 hzN]
    decide
  have hz4 : (c * y * c⁻¹) ^ 4 = t := by
    rw [conj_pow, hy4, comm_of htJ c, mul_inv_cancel_right]
  have hk : (nodeEl i)⁻¹ * (c * y * c⁻¹) ∈ phi6.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hphi, inv_mul_cancel]
  obtain ⟨nw, hnw⟩ := node4_ok hi
  rcases node4K_even hnw hev with ⟨x, hx, hmove⟩ | ⟨j, hj, hjS, hsq⟩
  · refine hmove (tab_pow4_fix (tab_node i hi) ?_ hx)
    rw [← hphi, ← map_pow, hz4, ht1]
  · have hrep : TabRep (unpack 1100 11 (EP.T j)) (phi6 (nodeEl i) * phi6 (nodeEl i)) := by
      rw [← hsq, ← CFSG.KC.BfsPin.compA_unpack (canon_T hi) (canon_T hi)]
      exact (tab_node i hi).comp (tab_node i hi)
    have hij : phi6 (nodeEl i ^ 2) = phi6 (nodeEl j) := by
      rw [map_pow, pow_two]
      exact hrep.perm_eq (tab_node j hj)
    have hk2 : (nodeEl j)⁻¹ * nodeEl i ^ 2 ∈ phi6.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hij, inv_mul_cancel]
    have hz2 := sq_eq_of_ker_gen ht2 (comm_of htJ _) (hker _ hk)
    have hi4 := sq_eq_of_ker_gen ht2 (comm_of htJ _) (hker _ hk2)
    have e4 : (c * y * c⁻¹) ^ 4 = ((c * y * c⁻¹) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e4, hz2, hi4, node_sq_one hj hjS] at hz4
    exact ne_one_of htJ hz4.symm

end Glue

theorem pow4_facts :
    ∀ y : CFSG.Sporadic.HNOddCore.C6,
      y ∈ CFSG.Sporadic.HNOddCore.Dsub.comap CFSG.Sporadic.HNOddCore.phi6 →
      y ^ 4 = CFSG.Sporadic.HNOddCore.t6C → False := by
  exact pow4_contra _ CertificateChecks.KernelHN25550.coe_t6C
    (MonoidHom.mem_ker.1 CFSG.Sporadic.HNOddCore.t6C_mem_ker)
    fun _ hk => CertificateChecks.KernelHN25550.ker_eq hk

end CertificateChecks.KernelHN27600

end
