module

public import Certificates.Kernel.ThCensus.Regs
public import Certificates.Kernel.ThCensus.Blocks
public import Certificates.Kernel.ThCensus.Orbit
public import Certificates.Kernel.ThCensus.Enum
public import Certificates.Kernel.ThCensus.Fus
public import Certificates.Kernel.ThCensus.Census0
public import Certificates.Kernel.ThCensus.Census1
public import Certificates.Kernel.ThCensus.Letters
public import CFSG.Certificates.Kernel.ThCensus.CensusSound
public import CFSG.Certificates.Kernel.Th.Spec.SylowOrbit
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
import CFSG.Certificates.Kernel.DceLoops
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Certificates.Kernel.Th.Spec.SylowPc

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThCensus CFSG.KD.ThCensus
  CFSG.KD.ThCensusW CFSG.KC.ThCensus.Sound

#kc_forall_tree ch17305Rall (fun i => ch17305R i = true) 3 CertificateChecks.KernelThCensus.ch17305R
#kc_forall_tree ch17305Ball (fun b => ch17305B b = true) 7 CertificateChecks.KernelThCensus.ch17305B
#kc_forall_tree ch17305Oall (fun k => ch17305O k = true) 10 CertificateChecks.KernelThCensus.ch17305O
#kc_forall_tree ch17305Tall (fun k => ch17305T k = true) 10 CertificateChecks.KernelThCensus.ch17305T
#kc_forall_tree ch17305Qall (fun b => ch17305Q b = true) 81 CertificateChecks.KernelThCensus.ch17305Q
#kc_forall_tree ch17305Fall (fun k => ch17305F k = true) 50 CertificateChecks.KernelThCensus.ch17305F
#kc_forall_tree ch17305Call (fun j => ch17305C j = true) 28 CertificateChecks.KernelThCensus.ch17305C
#kc_forall_tree ch17305Kall (fun j => ch17305K j = true) 28 CertificateChecks.KernelThCensus.ch17305K

theorem slpStart_ge (Cs : List ℕ) : ∀ i, 3 ≤ slpStart Cs i
  | 0 => le_rfl
  | i + 1 => by
    change 3 ≤ slpStart Cs i + Nat.land (Cs.getD i 0) 255
    have := slpStart_ge Cs i
    omega

theorem lt_of_inLayout {v : ℕ} (h : inLayout CFSG.KD.ThS.rm v = true) : v < 2 ^ 248 := by
  obtain ⟨-, hrm, -⟩ := consts_spec CFSG.KD.ThS.k0
  have e : Nat.land v CFSG.KD.ThS.rm = v := Nat.eq_of_beq_eq_true h
  rw [hrm] at e
  change v &&& (2 ^ 248 - 1) = v at e
  rw [Nat.and_two_pow_sub_one_eq_mod] at e
  rw [← e]
  exact Nat.mod_lt _ (by positivity)

section Facts

variable {G : Type*} [Group G] [Finite G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)}
  (hφ : Function.Injective φ) {a b : G} (ha : φ a = pkMat (RB 1)) (hb : φ b = pkMat (RB 2))
include hφ ha hb

theorem regs_elem : ∀ r, 0 < r → r < nreg → ∃ u : G, φ u = pkMat (RB r) := by
  have hk := CFSG.KD.ThS.k0
  obtain ⟨hL1, hL⟩ := Dce.andB_iff.1 ch17305L
  obtain ⟨hL2, -⟩ := Dce.andB_iff.1 hL
  let Qp : ℕ → Prop := fun k => ∃ u : G, φ u = pkMat (RB k)
  have hmul : ∀ r x y, Qp x → Qp y → RB r = mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (RB x) (RB y) →
      Qp r := by
    rintro r x y ⟨u, hu⟩ ⟨v, hv⟩ h
    exact ⟨u * v, by rw [map_mul, hu, hv, h, pkMat_mulB hk]⟩
  have hpow : ∀ r x e, Qp x → 0 < e → e < 16 →
      RB r = powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (RB x) e 4 → Qp r := by
    rintro r x e ⟨u, hu⟩ _ he h
    exact ⟨u ^ e, by rw [map_pow, hu, h, pkMat_powB hk _ e 4 (by norm_num; omega)]⟩
  have hinv : ∀ r x, Qp x → mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (RB x) (RB r) = CFSG.KD.ThS.ONE →
      Qp r := by
    rintro r x ⟨u, hu⟩ h
    refine ⟨u⁻¹, ?_⟩
    have h1 : pkMat (RB x) * pkMat (RB r) = 1 := by rw [← pkMat_mulB hk, h, pkMat_one hk]
    have h2 : φ u⁻¹ * pkMat (RB x) = 1 := by rw [← hu, ← map_mul, inv_mul_cancel, map_one]
    calc φ u⁻¹ = φ u⁻¹ * (pkMat (RB x) * pkMat (RB r)) := by rw [h1, Matrix.mul_one]
      _ = (φ u⁻¹ * pkMat (RB x)) * pkMat (RB r) := (Matrix.mul_assoc _ _ _).symm
      _ = pkMat (RB r) := by rw [h2, Matrix.one_mul]
  have chunk : ∀ i < 3, (∀ k, 0 < k → k < slpStart slp i → Qp k) →
      ∀ k, 0 < k → k < slpStart slp (i + 1) → Qp k := by
    intro i hi hS
    have e : runSlp RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE [slp.getD i 0] (slpStart slp i) =
        slpStart slp (i + 1) := Nat.eq_of_beq_eq_true (ch17305Rall i hi)
    have hpos : 0 < runSlp RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE [slp.getD i 0]
        (slpStart slp i) := by
      rw [e]
      have := slpStart_ge slp (i + 1)
      omega
    have h := FwdSlp.runSlp_induct Qp hmul hpow hinv [slp.getD i 0] (slpStart slp i) hS hpos
    rw [e] at h
    exact h
  have h0 : ∀ k, 0 < k → k < slpStart slp 0 → Qp k := by
    intro k hk0 hk3
    have hk3' : k < 3 := hk3
    rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
  have h3 := chunk 2 (by norm_num) (chunk 1 (by norm_num) (chunk 0 (by norm_num) h0))
  rw [Nat.eq_of_beq_eq_true hL2] at h3
  exact h3

theorem census_facts {Z S U : G} (hZ : φ Z = pkMat (RB regZ)) (hS : φ S = pkMat (RB regS))
    (hU : φ U = pkMat (RB regU)) :
    orderOf Z = 3 ∧ orderOf S = 3 ∧ orderOf U = 3 ∧ ∃ Q : Subgroup G, Nat.card Q = 3 ^ 10 ∧
      ∀ x ∈ Q, orderOf x = 3 → ∃ k C : G,
        (C = Z ∨ C = Z ^ 2 ∨ C = S ∨ C = S ^ 2 ∨ C = U ∨ C = U ^ 2) ∧ k * C * k⁻¹ = x := by
  have hk := CFSG.KD.ThS.k0
  have hreg := regs_elem hφ ha hb
  obtain ⟨-, hL⟩ := Dce.andB_iff.1 ch17305L
  obtain ⟨-, hL⟩ := Dce.andB_iff.1 hL
  obtain ⟨hpr, hL⟩ := Dce.andB_iff.1 hL
  obtain ⟨hX1, hL⟩ := Dce.andB_iff.1 hL
  obtain ⟨hX2, hL⟩ := Dce.andB_iff.1 hL
  obtain ⟨hB2, -⟩ := Dce.andB_iff.1 hL
  have below : ∀ r, regBelow r nreg = true → ∃ u : G, φ u = pkMat (RB r) := by
    intro r hr
    obtain ⟨h1, h2⟩ := Dce.andB_iff.1 hr
    exact hreg r (Nat.blt_eq.mp h1) (Nat.blt_eq.mp h2)
  have hprs := SylowOrbit.regsIn_spec hpr
  have hex : ∀ k, ∃ u : G, k < 10 → φ u = pkMat (RB (regAt pr k)) := by
    intro k
    by_cases hk10 : k < 10
    · obtain ⟨u, hu⟩ := hreg _ (hprs k hk10).1 (hprs k hk10).2
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hk10⟩
  choose g hg' using hex
  have hg : ∀ k < 10, φ (g k) = pkMat (RB (regAt pr k)) := fun k hk' => hg' k hk'
  have hpw : pwOK RB PW CFSG.KD.ThS.c CFSG.KD.ThS.rm pr 10 3 = true := ch17305W
  have hrun : runPc RB PW CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE pr 10 3 2 pc 1 = 10 + 1 :=
    Nat.eq_of_beq_eq_true ch17305P
  have hpc : ∀ i j, i ≤ j → j < 10 → (i = j → g i ^ 3 ∈ SylowPc.pcSub g 10 (i + 1)) ∧
      (i < j → (g i)⁻¹ * g j * g i ∈ SylowPc.pcSub g 10 (i + 1)) := by
    intro i j hij hj
    obtain ⟨x, hx⟩ := SylowPc.runPc_pairs (by norm_num) hrun i j hij hj
    exact SylowPc.pcRel_spec φ hφ hk (by norm_num) g hg hpw hij hj hx
  have hpow : ∀ i < 10, g i ^ 3 ∈ SylowPc.pcSub g 10 (i + 1) :=
    fun i hi => (hpc i i le_rfl hi).1 rfl
  have hconj : ∀ i j, i < j → j < 10 → (g i)⁻¹ * g j * g i ∈ SylowPc.pcSub g 10 (i + 1) :=
    fun i j hij hj => (hpc i j hij.le hj).2 hij
  have hup := SylowPc.pc_card_dvd φ hφ hk (by norm_num) (by norm_num) g hg hpw hrun
  obtain ⟨hnb, hbl⟩ := Dce.andB_iff.1 ch17305G
  have hnb' : nb = 7 := Nat.eq_of_beq_eq_true hnb
  have hblk : ∀ b' < nb, SylowOrbit.BlockOK RB CFSG.KD.ThS.rm pr 10 3 bl b' := by
    intro b' hb'
    have h := ch17305Ball b' (lt_of_lt_of_eq hb' hnb')
    obtain ⟨h1, h2⟩ := Dce.andB_iff.1 h
    obtain ⟨h3, h4⟩ := Dce.andB_iff.1 h2
    obtain ⟨h5, h6⟩ := Dce.andB_iff.1 h4
    exact ⟨fun k => PTS (boff.getD b' 0 + k), btree.getD b' [], bsrt.getD b' [], _,
      lt_of_inLayout h1, h3, Nat.eq_of_beq_eq_true h5, rfl, Nat.eq_of_beq_eq_true h6⟩
  have hlow := SylowOrbit.pow_le_card_closure hk hφ hg hbl hblk
  have hcard : Nat.card (SylowPc.pcSub g 10 0) = 3 ^ 10 :=
    Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hup) hlow
  let vec : ℕ → Fin 248 → ZMod 2 := fun p => pkVec (PTS (ooff + p))
  have htabs : ∀ k < 10, (tab.getD k []).length = 243 ∧ ∀ p < 243,
      (tab.getD k []).getD p 0 < 243 ∧ inLayout CFSG.KD.ThS.rm (PTS (ooff + p)) = true ∧
      vecB CFSG.KD.ThS.rm (PTS (ooff + p)) (RB (regAt pr k)) =
        PTS (ooff + (tab.getD k []).getD p 0) := by
    intro k hk'
    obtain ⟨h1, h2⟩ := Dce.andB_iff.1 (ch17305Oall k hk')
    have hlen : (tab.getD k []).length = 243 := by
      rw [← lenN_eq]
      exact Nat.eq_of_beq_eq_true h1
    refine ⟨hlen, fun p hp => ?_⟩
    have h := tabRow_spec _ 0 h2 p (by omega)
    rw [Nat.zero_add] at h
    exact h
  have hstep := step_of_tables φ g vec (PM 0) (fun k p => (tab.getD k []).getD p 0)
    (fun k hk' p hp => by
      have h := ttRow_spec _ 0 (ch17305Tall k hk') p (by rw [(htabs k hk').1]; exact hp)
      rw [Nat.zero_add] at h
      exact h)
    (fun k hk' p hp => by
      obtain ⟨h1, -, h3⟩ := (htabs k hk').2 p hp
      refine ⟨h1, ?_⟩
      change pkVec (PTS (ooff + (tab.getD k []).getD p 0)) =
        Matrix.vecMul (pkVec (PTS (ooff + p))) (φ (g k))
      rw [← h3, pkVec_vecB hk, hg k hk'])
  obtain ⟨hD, hD'⟩ := Dce.andB_iff.1 ch17305D
  obtain ⟨-, hD'⟩ := Dce.andB_iff.1 hD'
  obtain ⟨-, hD'⟩ := Dce.andB_iff.1 hD'
  obtain ⟨ho0, hD'⟩ := Dce.andB_iff.1 hD'
  obtain ⟨ho1, ho2⟩ := Dce.andB_iff.1 hD'
  have hinj : ∀ p < 243, ∀ q < 243, vec p = vec q → p = q := by
    intro p hp q hq e
    have hs := (CFSG.Certificates.DceLoop.sortRun_spec (get := fun j => PTS (ooff + j)) (qb := 8)
      (m := 243) (Cs := osrt) (S1 := DceS.runSorted (fun j => PTS (ooff + j)) 8 243 osrt 1) rfl
      (Nat.eq_of_beq_eq_true hD)).2
    refine hs p hp q hq (pkVec_inj ?_ ?_ e)
    · exact lt_of_inLayout ((htabs 0 (by norm_num)).2 p hp).2.1
    · exact lt_of_inLayout ((htabs 0 (by norm_num)).2 q hq).2.1
  have hsurj : ∀ x ∈ SylowPc.pcSub g 10 0, ∃ m < 3 ^ 10, nfFrom g 10 0 m = x :=
    nf_surj g 10 hpow hconj 10 0 rfl
  obtain ⟨hmove, hrec⟩ := blocks_spec (TT := PM 0) (R := fun b => PM (Nat.succ b))
    (reps := reps) (nr := lenN reps) (o0 := base.getD 0 0) (o1 := base.getD 1 0)
    (o2 := base.getD 2 0) ch17305Qall
  have hconjQ := fun (x : G) (hx : x ∈ SylowPc.pcSub g 10 0) (h3 : x ^ 3 = 1) =>
    conj_spec hstep hinj (Nat.blt_eq.mp ho0) (Nat.blt_eq.mp ho1) (Nat.blt_eq.mp ho2)
      hsurj hmove hrec hx h3
  have hpwS := SylowPc.pw_spec φ hk g hg hpw
  obtain ⟨hI1, hI⟩ := Dce.andB_iff.1 ch17305I
  obtain ⟨hI2, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨hI3, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨hI4, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨hI5, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨hI6, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨-, hI8⟩ := Dce.andB_iff.1 hI
  have hnr : lenN reps = 56 := Nat.eq_of_beq_eq_true hI1
  have hnt : tgts.length = 28 := by
    rw [← lenN_eq]
    exact Nat.eq_of_beq_eq_true hI2
  have hfl : fus.length = 50 := by
    rw [← lenN_eq]
    exact Nat.eq_of_beq_eq_true hI5
  have hreps := rep_conj hk hφ hpwS hZ hS hU (WC := fun j => WD (Nat.add 50 j)) (WF := WD)
    ⟨a, ha⟩ ⟨b, hb⟩ (below _ hB2) (below _ hX1) (below _ hX2) hnt
    (by rw [← lenN_eq, hnr]) hI3 hI4 (fun j hj => ch17305Call j hj)
    (fun j hj => ch17305Kall j hj) (fun k hk' => ch17305Fall k (lt_of_lt_of_eq hk' hfl)) hI6 hI8
  obtain ⟨hz1, hz⟩ := Dce.andB_iff.1 ch17305Z
  obtain ⟨hs1, hu1⟩ := Dce.andB_iff.1 hz
  refine ⟨ord3_spec hk hφ hZ hz1, ord3_spec hk hφ hS hs1, ord3_spec hk hφ hU hu1,
    SylowPc.pcSub g 10 0, hcard, fun x hx ho => ?_⟩
  rw [hnr] at hconjQ
  exact census_of_reps (Q := SylowPc.pcSub g 10 0) (nr := 56)
    (fun y hy h3 => hconjQ y hy h3) hreps hx ho

end Facts

end CertificateChecks.KernelThCensus

end
