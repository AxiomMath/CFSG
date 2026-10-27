
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtOG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtLF
public import CFSG.Certificates.Kernel.Spor.BTupSSound
public import CFSG.Certificates.Kernel.Spor.ConjCount
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Fin
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtLG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG
  CertificateChecks.KernelSpor.SuzBtNG CertificateChecks.KernelSpor.SuzBtOG

theorem kCj : allN 45 (fun k => btCjSK 1782 11 (mask 11) 3 SuzBtL1.cnt SuzBtL1.B SuzBtL1.G
    SuzBtL1.R SuzBtLC.PRE SuzBtLC.SV (decK (SuzBtLC.W.getD k [], 0)) k) = true := by quickRfl

theorem kW : SuzBtLC.W.length = 45 ∧ ∀ w ∈ SuzBtLC.W, ∀ i ∈ w, i < 10 := by decide

noncomputable abbrev LL : Subgroup (Equiv.Perm (Fin 1782)) := genSub 1782 4 lgp

theorem hfixL : ∀ h ∈ LL, (∀ t, h (c1Base t) = c1Base t) → h = 1 :=
  fun _ hh hf => invE1_eq_one (l1_le hh) hf

theorem st_lt (s : Fin 16) : (s : Nat) < SuzBtL1.cnt := by
  rw [SuzBtZF.kL1Cnt]
  exact s.2

theorem st_ex (s : Fin 16) : ∃ h ∈ LL, ∀ t : Fin 3,
    pg 11 (mask 11) (btKey 33 (mask 33) SuzBtL1.K s) t = h (c1Base t) :=
  btKey_mem hgL hbL hpL (st_lt s)

@[expose] noncomputable def xs (s : Fin 16) : Equiv.Perm (Fin 1782) := Classical.choose (st_ex s)

theorem xs_mem (s : Fin 16) : xs s ∈ LL := (Classical.choose_spec (st_ex s)).1

theorem xs_key (s : Fin 16) (t : Fin 3) :
    pg 11 (mask 11) (btKey 33 (mask 33) SuzBtL1.K s) t = xs s (c1Base t) :=
  (Classical.choose_spec (st_ex s)).2 t

theorem xs_inj {s s' : Fin 16} (h : xs s = xs s') : s = s' :=
  Fin.ext (btKey_inj (by norm_num) hpL (st_lt s) (st_lt s') fun t => by
    rw [xs_key, xs_key, h])

theorem xs_surj {y : Equiv.Perm (Fin 1782)} (hy : y ∈ LL) : ∃ s, xs s = y := by
  obtain ⟨i, hi, he⟩ := btKey_cover hgL hbL hpL SuzBtZF.kL1Hd hy
  have hi' : i < 16 := by rw [SuzBtZF.kL1Cnt] at hi; exact hi
  refine ⟨⟨i, hi'⟩, invE1_ext (l1_le (xs_mem _)) (l1_le hy) fun t => Fin.ext ?_⟩
  rw [← xs_key ⟨i, hi'⟩ t]
  exact he t

theorem hpreN {j : Nat} (hj : j < 2) (t : Fin 3) :
    ∃ hl : btPre SuzBtM1O.PRE 3 j t < 1782, ngp j ⟨_, hl⟩ = c1Base t := by
  obtain ⟨hl, he⟩ := btPre_spec SuzBtOF.kPre hj t.2
  refine ⟨hl, Fin.ext ?_⟩
  rw [← hCN j hj, he, hbM t]

theorem ngp_mem {j : Nat} (hj : j < 2) : ngp j ∈ invE 1 := nl1_le (gp_mem hj)

theorem conj_xs {j : Nat} (hj : j < 2) (s : Fin 16) :
    ∃ hu : pg 4 (mask 4) (SuzBtLS.G j) s < 16,
      xs ⟨_, hu⟩ = ngp j * xs s * (ngp j)⁻¹ := by
  have h := btSg_spec hgL hpL hfixL hbL (hCN j hj) (hpreN hj)
    (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtLF.kSg j hj) (st_lt s) (xs_mem s) (xs_key s)
  have hu : pg 4 (mask 4) (SuzBtLS.G j) s < 16 := by
    have := h.1
    rwa [SuzBtZF.kL1Cnt] at this
  refine ⟨hu, invE1_ext (l1_le (xs_mem _)) (Subgroup.mul_mem _ (Subgroup.mul_mem _ (ngp_mem hj)
    (l1_le (xs_mem s))) (Subgroup.inv_mem _ (ngp_mem hj))) fun t => Fin.ext ?_⟩
  rw [← xs_key ⟨_, hu⟩ t]
  exact h.2 t

theorem isPerm_sg {j : Nat} (hj : j < 2) : PK.IsPermN 16 (fun x => pg 4 (mask 4) (SuzBtLS.G j) x) := by
  refine ⟨fun x hx => (conj_xs hj ⟨x, hx⟩).1, fun x hx y hy hxy => ?_⟩
  obtain ⟨hu, eu⟩ := conj_xs hj ⟨x, hx⟩
  obtain ⟨hv, ev⟩ := conj_xs hj ⟨y, hy⟩
  have e1 : xs ⟨_, hu⟩ = xs ⟨_, hv⟩ := congrArg xs (Fin.ext hxy)
  rw [eu, ev] at e1
  have e2 : xs ⟨x, hx⟩ = xs ⟨y, hy⟩ := by
    have := congrArg (fun z => (ngp j)⁻¹ * z * ngp j) e1
    simpa [mul_assoc] using this
  exact congrArg Fin.val (xs_inj e2)

@[expose] noncomputable def sgP (j : Nat) : Equiv.Perm (Fin 16) :=
  PK.permOf 16 (fun x => pg 4 (mask 4) (SuzBtLS.G j) x)

theorem hgS : ∀ j < 2, ∀ x : Fin 16, pg 4 (mask 4) (SuzBtLS.G j) x = sgP j x :=
  fun j hj x => (PK.permOf_apply (isPerm_sg hj) x).symm

theorem sgP_xs {j : Nat} (hj : j < 2) (s : Fin 16) :
    xs (sgP j s) = ngp j * xs s * (ngp j)⁻¹ := by
  obtain ⟨hu, eu⟩ := conj_xs hj s
  rw [← eu]
  exact congrArg xs (Fin.ext (hgS j hj s).symm)

theorem lift {h : Equiv.Perm (Fin 16)} (hh : h ∈ genSub 16 2 sgP) :
    ∃ ν ∈ genSub 1782 2 ngp, ∀ s, xs (h s) = ν * xs s * ν⁻¹ := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨ngp j, gp_mem hj, sgP_xs hj⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun s => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨ν, hν, ex⟩ := hx
    obtain ⟨μ, hμ, ey⟩ := hy
    refine ⟨ν * μ, Subgroup.mul_mem _ hν hμ, fun s => ?_⟩
    rw [Equiv.Perm.mul_apply, ex, ey]
    group
  | inv x _ hx =>
    obtain ⟨ν, hν, ex⟩ := hx
    refine ⟨ν⁻¹, Subgroup.inv_mem _ hν, fun s => ?_⟩
    have e := ex (x⁻¹ s)
    have e0 : x (x⁻¹ s) = s := by simp
    rw [e0] at e
    rw [e]
    group

@[expose] noncomputable def sb (i : Fin 4) : Fin 16 :=
  ⟨pg 4 (mask 4) SuzBtLS.B i % 16, Nat.mod_lt _ (by norm_num)⟩

theorem kSB_at (i : Fin 4) : pg 4 (mask 4) SuzBtLS.B i < 16 ∧ btMov 11 (mask 11) 3 (SuzBtL1.G i)
    SuzBtL1.B (btKey 33 (mask 33) SuzBtL1.K (pg 4 (mask 4) SuzBtLS.B i)) = true := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtLF.kSB i i.2
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  have h1 := Nat.blt_eq.mp h.1
  rw [SuzBtZF.kL1Cnt] at h1
  exact ⟨h1, h.2⟩

theorem hbS : ∀ t : Fin 4, pg 4 (mask 4) SuzBtLS.B t = sb t := fun t =>
  (Nat.mod_eq_of_lt (kSB_at t).1).symm

theorem xs_sb (i : Fin 4) : xs (sb i) = lgp i := by
  refine invE1_ext (l1_le (xs_mem _)) (l1_le (gp_mem i.2)) fun t => Fin.ext ?_
  rw [← xs_key, ← mov_base hbL (hgL i i.2) (kSB_at i).2 t]
  change _ = pg 11 (mask 11) (btKey 33 (mask 33) SuzBtL1.K (pg 4 (mask 4) SuzBtLS.B i)) t
  rw [hbS i]

theorem hpS : ∀ i < SuzBtLS.cnt, btPtK 16 4 (mask 4) 4 16 (mask 16) 2 SuzBtLS.cnt SuzBtLS.B
    SuzBtLS.G SuzBtLS.K SuzBtLS.R SuzBtLS.POS i = true := fun i hi =>
  btSl_spec SuzBtLF.kLSl (Nat.zero_le _) (by rw [SuzBtLF.kLCnt] at hi; omega) hi

theorem rs_ex (r : Fin 24) : ∃ ν ∈ genSub 1782 2 ngp, ∀ i : Fin 4,
    (pg 4 (mask 4) (btKey 16 (mask 16) SuzBtLS.K r) i : Nat) = ((⟨_, (ptFacts (hpS r (by
      rw [SuzBtLF.kLCnt]; exact r.2))).lt i i.2⟩ : Fin 16) : Nat) ∧
    xs ⟨_, (ptFacts (hpS r (by rw [SuzBtLF.kLCnt]; exact r.2))).lt i i.2⟩ =
      ν * lgp i * ν⁻¹ := by
  have hr : (r : Nat) < SuzBtLS.cnt := by rw [SuzBtLF.kLCnt]; exact r.2
  obtain ⟨h, hh, he⟩ := btKey_mem hgS hbS hpS hr
  obtain ⟨ν, hν, eν⟩ := lift hh
  refine ⟨ν, hν, fun i => ⟨rfl, ?_⟩⟩
  have e1 : (⟨_, (ptFacts (hpS r hr)).lt i i.2⟩ : Fin 16) = h (sb i) := Fin.ext (he i)
  rw [e1, eν, xs_sb]

@[expose] noncomputable def nn (r : Fin 24) : Equiv.Perm (Fin 1782) := Classical.choose (rs_ex r)

theorem nn_mem (r : Fin 24) : nn r ∈ genSub 1782 2 ngp := (Classical.choose_spec (rs_ex r)).1

theorem nn_inj (r r' : Fin 24) (h : ∀ i : Fin 4, nn r * lgp i * (nn r)⁻¹ = nn r' * lgp i * (nn r')⁻¹) :
    r = r' := by
  have hr : (r : Nat) < SuzBtLS.cnt := by rw [SuzBtLF.kLCnt]; exact r.2
  have hr' : (r' : Nat) < SuzBtLS.cnt := by rw [SuzBtLF.kLCnt]; exact r'.2
  refine Fin.ext (btKey_inj (by norm_num) hpS hr hr' fun t => ?_)
  have e1 := ((Classical.choose_spec (rs_ex r)).2 t).2
  have e2 := ((Classical.choose_spec (rs_ex r')).2 t).2
  have e3 := xs_inj (e1.trans ((h t).trans e2.symm))
  exact congrArg Fin.val e3

@[expose] noncomputable def gk (k : Fin 45) : Equiv.Perm (Fin 1782) :=
  decPerm (SuzBtLC.W.getD k [], 0)

theorem W_ok (k : Fin 45) : ∀ i ∈ (SuzBtLC.W.getD k [], 0).1, i < 10 := by
  intro i hi
  have hk : (k : Nat) < SuzBtLC.W.length := by rw [kW.1]; exact k.2
  rw [List.getD_eq_getElem _ _ hk] at hi
  exact kW.2 _ (List.getElem_mem hk) i hi

theorem gk_mem (k : Fin 45) : gk k ∈ invE 1 := decPerm_mem (W_ok k)

@[expose] noncomputable def kp (y : Equiv.Perm (Fin 1782)) : Nat := btKf 11 c1Base y

@[expose] noncomputable def xsN (s : Nat) : Equiv.Perm (Fin 1782) :=
  if h : s < 16 then xs ⟨s, h⟩ else 1

theorem sum_gk (k : Fin 45) :
    ∑ s ∈ Finset.range 16, kp (gk k * xsN s * (gk k)⁻¹) = btSv SuzBtLC.SV k := by
  have h := btCjSK_spec hgL hpL hfixL hbL (pg_decK (W_ok k) (by norm_num)) hbL
    (CFSG.KS.Raw.Orb.allN_iff.1 kCj k k.2) (y := xsN)
    (fun s hs => by
      rw [SuzBtZF.kL1Cnt] at hs
      unfold xsN
      rw [dif_pos hs]
      exact xs_mem _)
    (fun s hs t => by
      rw [SuzBtZF.kL1Cnt] at hs
      unfold xsN
      rw [dif_pos hs]
      exact xs_key ⟨s, hs⟩ t)
  rw [SuzBtZF.kL1Cnt] at h
  exact h.2

noncomputable instance : Fintype LL := Fintype.ofFinite _

theorem sumConj_gk (k : Fin 45) : ConjCount.sumConj LL kp (gk k) = btSv SuzBtLC.SV k := by
  rw [← sum_gk k, ConjCount.sumConj]
  rw [← Fin.sum_univ_eq_sum_range (fun s => kp (gk k * xsN s * (gk k)⁻¹))]
  refine (Fintype.sum_bijective (fun s : Fin 16 => (⟨xs s, xs_mem s⟩ : LL))
    ⟨fun a b e => xs_inj (congrArg Subtype.val e), fun y => ?_⟩ _ _ fun s => ?_).symm
  · obtain ⟨s, hs⟩ := xs_surj y.2
    exact ⟨s, Subtype.ext hs⟩
  · change kp (gk k * xsN s * (gk k)⁻¹) = kp (gk k * xs s * (gk k)⁻¹)
    unfold xsN
    rw [dif_pos s.2]

theorem gk_sep (k k' : Fin 45) (h : ConjCount.sumConj LL kp (gk k) = ConjCount.sumConj LL kp (gk k')) :
    k = k' := by
  rw [sumConj_gk, sumConj_gk] at h
  rcases Nat.lt_trichotomy k k' with h' | h' | h'
  · exact absurd h (Nat.ne_of_lt (btInc_spec SuzBtLF.kInc h' k'.2))
  · exact Fin.ext h'
  · exact absurd h.symm (Nat.ne_of_lt (btInc_spec SuzBtLF.kInc h' k.2))

theorem basis_eq (i : Fin 4) : l1BasisPerm i.val = lgp i := by
  have hi : (i : Nat) < l1Decs.length := by
    rw [show l1Decs.length = 4 from rfl]
    exact i.2
  unfold l1BasisPerm lgp
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]

theorem l1_closure : LL = Subgroup.closure (Set.range fun i : Fin 4 => l1BasisPerm i.val) := by
  unfold LL genSub
  congr 1
  ext g
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, basis_eq ⟨j, hj⟩⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, (basis_eq i).symm⟩

theorem card_C1 : Nat.card ↥(invE 1) = 45 * 24 * 3072 := by
  rw [card_invE (i := 1) (by norm_num)]
  rfl

theorem f2Prop : F2Prop := by
  have hN : ∀ r, nn r ∈ Subgroup.normalizer (LL : Set (Equiv.Perm (Fin 1782))) := fun r => by
    rw [LL, l1_eq]
    exact nl1_le_norm (nl1_eq ▸ nn_mem r)
  have hCL : decSubgroup cl1Decs ≤ Subgroup.centralizer (LL : Set (Equiv.Perm (Fin 1782))) ⊓
      invE 1 := by
    rw [LL, l1_eq]
    exact cl1_le_inf
  obtain ⟨hC, hO, hS⟩ := ConjCount.conj_count (ι := Fin 4)
    (b := fun i : Fin 4 => l1BasisPerm i.val) (A := invE 1) (L := LL)
    (CL := decSubgroup cl1Decs) (kp := kp) (gk := gk) (nn := nn) l1_closure card_C1 gk_mem
    gk_sep (fun r => nl1_le (nn_mem r)) hN
    (fun r r' h => nn_inj r r' fun i => by simpa [basis_eq] using h i) hCL card_CL1
  unfold F2Prop
  dsimp only
  rw [← l1_eq]
  exact ⟨hO, hS, hC, card_CL1, m1_normal, l1_eq ▸ nl1_le_norm⟩

end CertificateChecks.KernelSpor.SuzBtLG

end
