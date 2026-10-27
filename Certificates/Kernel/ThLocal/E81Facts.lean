module

public import Certificates.Kernel.ThLocal.E81Checks
public import Certificates.Kernel.ThLocal.Checks
public import Certificates.Kernel.ThCensus.Facts
public import CFSG.Certificates.Kernel.ThLocal.E81Sound
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Certificates.Kernel.DceLoops
import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.Group

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThLocal

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThCensus CFSG.KD.ThCensus
  CFSG.KD.ThCensusW CFSG.KC.ThCensus.Sound CFSG.KC.ThLocal CFSG.KC.ThLocal.Sound CFSG.KD.ThLocalE81
  CertificateChecks.KernelThCensus

#kc_forall_tree ch9521Rall (fun m => ch9521R m = true) 56 CertificateChecks.KernelThLocal.ch9521R

section Facts

variable {G : Type*} [Group G] [Finite G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)}
  (hφ : Function.Injective φ) {a b : G} (ha : φ a = pkMat (RB 1)) (hb : φ b = pkMat (RB 2))
include hφ ha hb

theorem e81_facts {Z : G} (hZ : φ Z = pkMat (RB regZ)) :
    ∃ Q : Subgroup G, Nat.card Q = 3 ^ 10 ∧ Z ∈ Q ∧ Z ^ 3 = 1 ∧ Z ≠ 1 ∧
      (∀ q ∈ Q, q * Z = Z * q) ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ∉ Subgroup.zpowers Z →
        ∃ E : Subgroup G, E ≤ Q ∧ CFSG.Open.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧
          Z ∈ E := by
  have hk := CFSG.KD.ThS.k0
  have hreg := regs_elem hφ ha hb
  obtain ⟨-, hL⟩ := Dce.andB_iff.1 ch17305L
  obtain ⟨-, hL⟩ := Dce.andB_iff.1 hL
  obtain ⟨hpr, -⟩ := Dce.andB_iff.1 hL
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
  have ho0' := Nat.blt_eq.mp ho0
  have ho1' := Nat.blt_eq.mp ho1
  have ho2' := Nat.blt_eq.mp ho2
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
    conj_spec hstep hinj ho0' ho1' ho2' hsurj hmove hrec hx h3
  have K3 := fun {c n r : ℕ} (h : key3 (PM 0) (base.getD 0 0) (base.getD 1 0) (base.getD 2 0)
    c n r = true) => key3_spec hstep hinj ho0' ho1' ho2' hsurj hmove h
  have C3 := fun {n : ℕ} (h : cube3 (PM 0) (base.getD 0 0) (base.getD 1 0) (base.getD 2 0) n =
    true) => cube3_spec hstep hinj ho0' ho1' ho2' hsurj hmove h
  obtain ⟨-, hzr⟩ := Dce.andB_iff.1 ch13650Z
  obtain ⟨hzc, -⟩ := Dce.andB_iff.1 ch13650Z
  have hZg : Z = g 9 := by
    apply hφ
    rw [hZ, hg 9 (by norm_num), Nat.eq_of_beq_eq_true hzr]
  obtain ⟨hz1, -⟩ := Dce.andB_iff.1 ch17305Z
  have oZ : orderOf Z = 3 := ord3_spec hk hφ hZ hz1
  have hZ3 : Z ^ 3 = 1 := by rw [← oZ]; exact pow_orderOf_eq_one Z
  have hZ1 : Z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at oZ
    exact absurd oZ (by norm_num)
  have hz9 : nfFrom g 10 0 19683 = Z := by rw [nfFrom_z, hZg]
  have hz92 : nfFrom g 10 0 39366 = Z ^ 2 := by rw [nfFrom_z2, hZg]
  have hzk : ∀ k < 10, g k * Z = Z * g k := by
    intro k hk'
    have e := K3 (zcOK_dec hzc k hk')
    rwa [nfFrom_pow3 g hk', hz9] at e
  have hZQ : Z ∈ SylowPc.pcSub g 10 0 := by
    rw [hZg]
    exact SylowPc.mem_pcSub (by norm_num) (by norm_num)
  have hcent : ∀ q ∈ SylowPc.pcSub g 10 0, q * Z = Z * q := by
    have hle : SylowPc.pcSub g 10 0 ≤ Subgroup.centralizer ({Z} : Set G) := by
      rw [SylowPc.pcSub, Subgroup.closure_le]
      rintro _ ⟨k, hk', rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hzk k hk'.2)
    exact fun q hq => Subgroup.mem_centralizer_singleton_iff.1 (hle hq)
  obtain ⟨hI1, -⟩ := Dce.andB_iff.1 ch17305I
  have hnr : lenN reps = 56 := Nat.eq_of_beq_eq_true hI1
  refine ⟨SylowPc.pcSub g 10 0, hcard, hZQ, hZ3, hZ1, hcent, fun s hs hs3 hsz => ?_⟩
  rw [hnr] at hconjQ
  rcases hconjQ s hs hs3 with h1 | ⟨m, hm, c, hcQ, hc⟩
  · rw [h1] at hsz
    exact absurd (one_mem _) hsz
  have hcz : c * Z = Z * c := hcent c hcQ
  have hsc : s = c⁻¹ * nfFrom g 10 0 (permNfNum (reps.getD m [])) * c := by
    rw [← hc]
    group
  have hR := ch9521Rall m hm
  rcases e81RepOK_dec hR with hz | he
  · exfalso
    apply hsz
    have hZc : c⁻¹ * Z * c = Z := by
      rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]
    rcases isZ_dec hz with e | e
    · rw [hsc, e, hz9, hZc]
      exact Subgroup.mem_zpowers Z
    · rw [hsc, e, hz92, pow_two]
      have e2 : c⁻¹ * (Z * Z) * c = (c⁻¹ * Z * c) * (c⁻¹ * Z * c) := by group
      rw [e2, hZc]
      exact mul_mem (Subgroup.mem_zpowers Z) (Subgroup.mem_zpowers Z)
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := e81OK_dec he
  set rn := permNfNum (reps.getD m []) with hrn
  set xn := (fe.getD m []).getD 0 0 with hxn
  set yn := (fe.getD m []).getD 1 0 with hyn
  have hxR := K3 u1
  have hyR := K3 u2
  have hxy := K3 u3
  have hx3 := C3 u4
  have hy3 := C3 u5
  have hmv := movesOK_dec u6
  set R := nfFrom g 10 0 rn with hRdef
  set x := nfFrom g 10 0 xn with hxdef
  set y := nfFrom g 10 0 yn with hydef
  have hR3 : R ^ 3 = 1 := by
    rw [← hc, conj_pow, hs3, mul_one, mul_inv_cancel]
  have hRZ : R * Z = Z * R := hcent R (nf_mem rn)
  have hZx : Z * x = x * Z := (hcent x (nf_mem xn)).symm
  have hZy : Z * y = y * Z := (hcent y (nf_mem yn)).symm
  have hne : ∀ u, u ≠ ((0, 0), (0, 0)) → quadP R Z x y u ≠ 1 := by
    intro u hu
    have h1 := u.1.1.isLt
    have h2 := u.1.2.isLt
    have h3 := u.2.1.isLt
    have h4 := u.2.2.isLt
    have hpos : 0 < u.1.1.val + 3 * u.1.2.val + 9 * u.2.1.val + 27 * u.2.2.val := by
      rcases Nat.eq_zero_or_pos (u.1.1.val + 3 * u.1.2.val + 9 * u.2.1.val + 27 * u.2.2.val)
        with h0 | h0
      · exfalso
        apply hu
        refine Prod.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
          simp <;> omega
      · exact h0
    set v := u.1.1.val + 3 * u.1.2.val + 9 * u.2.1.val + 27 * u.2.2.val with hv
    have hi := hmv (v - 1) (by omega)
    have hv1 : v - 1 + 1 = v := by omega
    rw [hv1] at hi
    have ea : v % 3 = u.1.1.val := by omega
    have eb : v / 3 % 3 = u.1.2.val := by omega
    have ec : v / 9 % 3 = u.2.1.val := by omega
    have ed : v / 27 = u.2.2.val := by omega
    have key : ∀ o < 243, moveAt (PM 0) o rn xn yn v = true → quadP R Z x y u ≠ 1 := by
      intro o ho hmo
      have hh := moveAt_spec hstep hinj ho hmo
      rw [ea, eb, ec, ed, hz9] at hh
      exact hh
    rcases Dce.orB_iff.1 hi with k | k
    · exact key _ ho0' k
    rcases Dce.orB_iff.1 k with k | k
    · exact key _ ho1' k
    · exact key _ ho2' k
  let f : G →* G := (MulAut.conj c⁻¹).toMonoidHom
  have hf : ∀ w, f w = c⁻¹ * w * c := fun w => by
    change c⁻¹ * w * c⁻¹⁻¹ = _
    rw [inv_inv]
  have finj : Function.Injective f := (MulAut.conj c⁻¹).injective
  have fc : ∀ {p q : G}, p * q = q * p → f p * f q = f q * f p := fun h => by
    rw [← map_mul, ← map_mul, h]
  have f3 : ∀ {p : G}, p ^ 3 = 1 → f p ^ 3 = 1 := fun h => by
    rw [← map_pow, h, map_one]
  have hfq : ∀ u, quadP (f R) (f Z) (f x) (f y) u = f (quadP R Z x y u) := fun u => by
    simp only [quadP, pairP, map_mul, map_pow]
  have hfR : f R = s := by rw [hf, hsc]
  have hfZ : f Z = Z := by
    rw [hf, mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]
  have key := e81_closure (fc hRZ) (fc hxR.symm) (fc hyR.symm) (fc hZx) (fc hZy) (fc hxy)
    (f3 hR3) (f3 hZ3) (f3 hx3) (f3 hy3)
    (fun u hu => by
      rw [hfq]
      exact fun e => hne u hu (finj (e.trans (map_one f).symm)))
  rw [hfR, hfZ] at key
  have hfQ : ∀ w ∈ SylowPc.pcSub g 10 0, f w ∈ SylowPc.pcSub g 10 0 := fun w hw => by
    rw [hf]
    exact mul_mem (mul_mem (inv_mem hcQ) hw) hcQ
  refine ⟨_, ?_, key.1, key.2, Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp)⟩
  rw [Subgroup.closure_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact hs
  · exact hZQ
  · exact hfQ _ (nf_mem xn)
  · exact hfQ _ (nf_mem yn)

end Facts

end CertificateChecks.KernelThLocal

end
