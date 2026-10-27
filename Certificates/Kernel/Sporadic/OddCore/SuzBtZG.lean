module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZF
public import CFSG.Certificates.Kernel.Spor.BTupRSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtZG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG

theorem kBL : allN 4 (fun j => Nat.beq (SuzBtL1.G j) (decK (l1Decs.getD j ([], 0)))) = true := by
  quickRfl

@[expose] noncomputable def mgp (j : Nat) : Equiv.Perm (Fin 1782) := decPerm (m1Decs.getD j ([], 0))

@[expose] noncomputable def lgp (j : Nat) : Equiv.Perm (Fin 1782) := decPerm (l1Decs.getD j ([], 0))


theorem l1Decs_ok {i : Nat} (hi : i < 4) : (∀ k ∈ (l1Decs.getD i ([], 0)).1, k < 10) ∧
    (l1Decs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem hgL : ∀ j < 4, ∀ x : Fin 1782, pg 11 (mask 11) (SuzBtL1.G j) x = lgp j x :=
  fun j hj x => by
    rw [Nat.eq_of_beq_eq_true (allN_spec kBL j hj)]
    exact pg_decK (l1Decs_ok hj).1 (l1Decs_ok hj).2 x

theorem hbL : ∀ t : Fin 3, pg 11 (mask 11) SuzBtL1.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem hpL : ∀ i < SuzBtL1.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtL1.cnt SuzBtL1.B
    SuzBtL1.G SuzBtL1.K SuzBtL1.R SuzBtL1.POS i = true := fun i hi =>
  btSl_spec SuzBtZF.kL1Sl (Nat.zero_le _) (by rw [SuzBtZF.kL1Cnt] at hi; omega) hi

theorem hpM : ∀ i < SuzBtM1.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 8 SuzBtM1.cnt SuzBtM1.B
    SuzBtM1.G SuzBtM1.K SuzBtM1.R SuzBtM1.POS i = true := fun i hi =>
  btSl_spec SuzBtF.kSl (Nat.zero_le _) (by rw [SuzBtF.kCnt] at hi; omega) hi

theorem mov_base {B Kq G : Nat} {g : Equiv.Perm (Fin 1782)}
    (hB : ∀ t : Fin 3, pg 11 (mask 11) B t = c1Base t)
    (hG : ∀ x : Fin 1782, pg 11 (mask 11) G x = g x) (h : btMov 11 (mask 11) 3 G B Kq = true) :
    ∀ t : Fin 3, pg 11 (mask 11) Kq t = g (c1Base t) := fun t => by
  rw [btMov_spec h t t.2, hB t, hG]


theorem l1_eq : genSub 1782 4 lgp = decSubgroup l1Decs := genSub_dec l1Decs

theorem m1_le : genSub 1782 8 mgp ≤ invE 1 := by
  rw [show genSub 1782 8 mgp = decSubgroup m1Decs from genSub_dec m1Decs]
  exact decSubgroup_le_invE (by decide)

theorem l1_le : genSub 1782 4 lgp ≤ invE 1 := by
  rw [l1_eq]
  exact decSubgroup_le_invE (by decide)

theorem mem_of_btKey {k kw km cnt base : Nat} {G K R POS : Nat → Nat}
    {gp : Nat → Equiv.Perm (Fin 1782)} (hle : genSub 1782 k gp ≤ invE 1)
    (hg : ∀ j < k, ∀ x : Fin 1782, pg 11 (mask 11) (G j) x = gp j x)
    (hb : ∀ t : Fin 3, pg 11 (mask 11) base t = c1Base t)
    (hp : ∀ i < cnt, btPtK 1782 11 (mask 11) 3 kw km k cnt base G K R POS i = true) {q : Nat}
    (hq : q < cnt) {x : Equiv.Perm (Fin 1782)} (hx : x ∈ invE 1)
    (he : ∀ t : Fin 3, pg 11 (mask 11) (btKey kw km K q) t = x (c1Base t)) :
    x ∈ genSub 1782 k gp := by
  obtain ⟨h, hh, he'⟩ := btKey_mem hg hb hp hq
  have e : x = h := invE1_ext hx (hle hh) fun t => Fin.ext (by rw [← he t, he' t])
  rw [e]
  exact hh

theorem l1_le_m1 : genSub 1782 4 lgp ≤ genSub 1782 8 mgp := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtZF.kT j hj
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact mem_of_btKey m1_le hgM hbM hpM (Nat.blt_eq.mp h.1) (l1_le (gp_mem hj))
    (mov_base hbM (hgL j hj) h.2)

theorem gen_comm {j l : Nat} (hj : j < 4) (hl : l < 8) : lgp j * mgp l = mgp l * lgp j := by
  refine invE1_ext (Subgroup.mul_mem _ (l1_le (gp_mem hj)) (m1_le (gp_mem hl)))
    (Subgroup.mul_mem _ (m1_le (gp_mem hl)) (l1_le (gp_mem hj))) fun t => Fin.ext ?_
  have h := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1
    (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtZF.kC j hj) l hl) t t.2)
  rw [hbM t, hgM l hl, hgL j hj, hgL j hj, hgM l hl] at h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact h

theorem l1_le_cent : genSub 1782 4 lgp ≤ Subgroup.centralizer (genSub 1782 8 mgp : Set _) := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  have hle : genSub 1782 8 mgp ≤ Subgroup.centralizer {lgp j} := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact gen_comm hj hl
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.1 (hle hy)) _ rfl).symm

theorem hfixM : ∀ h ∈ genSub 1782 8 mgp, (∀ t, h (c1Base t) = c1Base t) → h = 1 :=
  fun h hh hfix => invE1_eq_one (m1_le hh) hfix

theorem hSM : ∀ j < 8, ∀ t : Fin 3,
    pg 11 (mask 11) (btKey 33 (mask 33) SuzBtM1.K (SuzBtM1Z.S j)) t = mgp j (c1Base t) :=
  fun j hj => mov_base hbM (hgM j hj) (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtZF.kS j hj)

theorem mem_l1_of_comm {x : Equiv.Perm (Fin 1782)} (hx : x ∈ genSub 1782 8 mgp)
    (hcomm : ∀ j < 8, x * mgp j = mgp j * x) : x ∈ genSub 1782 4 lgp := by
  obtain ⟨q, hq, he⟩ := btCz_mem (m := 8) (Y := SuzBtM1.G) hgM hpM hfixM hbM hSM
    (fun i hi => btRtSl_spec SuzBtZF.kRt (Nat.zero_le _) (by rw [SuzBtF.kCnt] at hi; omega) hi)
    hgM (fun i hi => btCzSl_spec SuzBtZF.kCz (Nat.zero_le _)
      (by rw [SuzBtF.kCnt] at hi; omega) hi) SuzBtF.kHd hx hcomm
  exact mem_of_btKey l1_le hgL hbL hpL hq (m1_le hx) he

theorem f1mProp : F1MProp := by
  refine ⟨card_M1, fun x => ⟨fun hx => ?_, fun ⟨hx, hc⟩ => ?_⟩⟩
  · rw [← l1_eq] at hx
    rw [← genSub_dec m1Decs]
    refine ⟨l1_le_m1 hx, fun y hy => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (l1_le_cent hx) y hy).symm
  · rw [← genSub_dec m1Decs] at hx hc
    rw [← l1_eq]
    exact mem_l1_of_comm hx fun j hj => hc _ (gp_mem hj)

end CertificateChecks.KernelSpor.SuzBtZG

end
