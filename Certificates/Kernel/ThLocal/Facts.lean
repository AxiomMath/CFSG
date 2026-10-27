module

public import Certificates.Kernel.ThLocal.Checks
public import Certificates.Kernel.ThCensus.Facts
public import CFSG.Certificates.Kernel.ThLocal.Sound
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Certificates.Kernel.DceLoops
import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.Group

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThLocal

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThCensus CFSG.KD.ThCensus
  CFSG.KD.ThCensusW CFSG.KC.ThCensus.Sound CFSG.KC.ThLocal CFSG.KC.ThLocal.Sound CFSG.KD.ThLocal
  CertificateChecks.KernelThCensus

#kc_forall_tree ch13650Tall (fun j => ch13650T j = true) 28 CertificateChecks.KernelThLocal.ch13650T

section Facts

variable {G : Type*} [Group G] [Finite G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)}
  (hφ : Function.Injective φ) {a b : G} (ha : φ a = pkMat (RB 1)) (hb : φ b = pkMat (RB 2))
include hφ ha hb

theorem local_facts {Z : G} (hZ : φ Z = pkMat (RB regZ)) :
    ∃ Q : Subgroup G, Nat.card Q = 3 ^ 10 ∧ Z ∈ Q ∧ Z ^ 3 = 1 ∧ (∀ q ∈ Q, q * Z = Z * q) ∧
      (∃ u : G, orderOf u = 2 ∧ u * Z = Z * u) ∧
      ∀ s ∈ Q, orderOf s = 3 → ∃ t : G, IsConj s t ∧
        3 ^ 7 ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({t} : Set G) ∧ CFSG.Open.IsElemAbelian 3 E ∧
          Nat.card E = 9 ∧ ∀ x ∈ E, x ≠ 1 → IsConj x Z ∨ IsConj x (Z ^ 2) := by
  have hk := CFSG.KD.ThS.k0
  have hreg := regs_elem hφ ha hb
  obtain ⟨-, hL⟩ := Dce.andB_iff.1 ch17305L
  obtain ⟨-, hL⟩ := Dce.andB_iff.1 hL
  obtain ⟨hpr, hL⟩ := Dce.andB_iff.1 hL
  obtain ⟨hX1, hL⟩ := Dce.andB_iff.1 hL
  obtain ⟨hX2, -⟩ := Dce.andB_iff.1 hL
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
  obtain ⟨hzc, hzr⟩ := Dce.andB_iff.1 ch13650Z
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
  have hZ2 : Z ^ 2 ≠ 1 := by
    intro h
    have h1 : Z = 1 := by
      calc Z = Z ^ 3 * (Z ^ 2)⁻¹ := by group
        _ = 1 := by rw [hZ3, h, inv_one, one_mul]
    exact hZ1 h1
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
  have hl4 : ∀ x < 4, x < 4 → ∃ u : G, φ u = pkMat (RB (letR 1 2 regX1 regX2 x)) := by
    intro x hx _
    rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
    · exact below _ hX1
    · exact below _ hX2
  have hinv : ∃ u : G, orderOf u = 2 ∧ u * Z = Z * u := by
    obtain ⟨u, hu⟩ := wordR_spec hk hl4 invn invw CFSG.KD.ThS.ONE (wordLetOK_four _ _) 1
      (by rw [pkMat_one hk, map_one])
    obtain ⟨v1, v2, v3⟩ := invOK_dec ch13650V
    set Wm := wordR RB CFSG.KD.ThS.c CFSG.KD.ThS.rm 1 2 regX1 regX2 invn invw CFSG.KD.ThS.ONE
      with hWm
    have hsq : u ^ 2 = 1 := by
      apply hφ
      have e := congrArg pkMat (Nat.eq_of_beq_eq_true v1)
      rw [pkMat_mulB hk, hu, pkMat_one hk, ← map_mul, ← pow_two] at e
      rw [e, map_one]
    have hne : u ≠ 1 := by
      intro h1
      have e : mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm Wm CFSG.KD.ThS.ONE = CFSG.KD.ThS.ONE := by
        refine pkMat_inj (inLayout_mulB hk _ _) (inLayout_one hk) ?_
        rw [pkMat_mulB hk, hu, h1, map_one, pkMat_one hk, Matrix.mul_one]
      rw [e, Nat.beq_refl] at v2
      exact Bool.noConfusion v2
    have hcomm : u * Z = Z * u := by
      apply hφ
      have e := congrArg pkMat (Nat.eq_of_beq_eq_true v3)
      rw [pkMat_mulB hk, pkMat_mulB hk, hu, ← hZ, ← map_mul, ← map_mul] at e
      exact e
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨u, orderOf_eq_prime hsq hne, hcomm⟩
  have hpwS := SylowPc.pw_spec φ hk g hg hpw
  obtain ⟨hI1, hI⟩ := Dce.andB_iff.1 ch17305I
  obtain ⟨hI2, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨hI3, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨hI4, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨hI5, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨hI6, hI⟩ := Dce.andB_iff.1 hI
  obtain ⟨-, hI8⟩ := Dce.andB_iff.1 hI
  have hnr : lenN reps = 56 := Nat.eq_of_beq_eq_true hI1
  have hnrl : reps.length = 56 := by rw [← lenN_eq]; exact hnr
  have hnt : tgts.length = 28 := by
    rw [← lenN_eq]
    exact Nat.eq_of_beq_eq_true hI2
  have hfl : fus.length = 50 := by
    rw [← lenN_eq]
    exact Nat.eq_of_beq_eq_true hI5
  let R : ℕ → G := fun m => nfFrom g 10 0 (permNfNum (reps.getD m []))
  let T : ℕ → G := fun j => nfFrom g 10 0 (permNfNum (tgts.getD j []))
  have hfus : ∀ k < 50, IsConj (R ((fus.getD k []).getD 0 0)) (T ((fus.getD k []).getD 1 0)) ∧
      (fus.getD k []).getD 1 0 < 28 := by
    intro k hk'
    have he : fus.getD k [] ∈ fus := getD_mem [] (by omega)
    obtain ⟨hi, hj⟩ := fusIdxOK_spec fus hI6 _ he
    obtain ⟨W, hW⟩ := wordR_spec hk hl4 _ _ CFSG.KD.ThS.ONE (wordLetOK_four _ _) 1
      (by rw [pkMat_one hk, map_one])
    have hT := nfM_spec hk hpwS (g := g)
      (nfsOK_spec tgts hI4 _ (getD_mem [] (by omega : (fus.getD k []).getD 1 0 < tgts.length)))
    have hR := nfM_spec hk hpwS (g := g) (nfsOK_spec reps hI3 _
      (getD_mem [] (by omega : (fus.getD k []).getD 0 0 < reps.length)))
    have e := conj_of_conjEq hk hφ hR hT hW (ch17305Fall k (by omega))
    refine ⟨isConj_iff.2 ⟨W, ?_⟩, hj⟩
    change W * nfFrom g 10 0 (permNfNum (reps.getD ((fus.getD k []).getD 0 0) [])) * W⁻¹ =
      nfFrom g 10 0 (permNfNum (tgts.getD ((fus.getD k []).getD 1 0) []))
    rw [e, mul_inv_cancel_right]
  have hrt : ∀ m < 56, ∃ j < 28, IsConj (R m) (T j) := by
    intro m hm
    have hc := coverOK_dec hI8 m hm
    rcases Dce.orB_iff.1 hc with hc | hc
    · obtain ⟨e, he, hem⟩ := anyL_spec _ fus hc
      obtain ⟨kf, hkf, rfl⟩ := exists_getD_of_mem (d := []) he
      obtain ⟨h1, h2⟩ := hfus kf (by omega)
      rw [Nat.eq_of_beq_eq_true hem] at h1
      exact ⟨_, h2, h1⟩
    · obtain ⟨t, ht, hte⟩ := anyL_spec _ tgts hc
      obtain ⟨j, hj, rfl⟩ := exists_getD_of_mem (d := []) ht
      have hT := nfM_spec hk hpwS (g := g) (nfsOK_spec tgts hI4 _ ht)
      have hR := nfM_spec hk hpwS (g := g)
        (nfsOK_spec reps hI3 _ (getD_mem [] (by omega : m < reps.length)))
      have heq : nfM PW CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (tgts.getD j []) =
          nfM PW CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (reps.getD m []) := by
        unfold nfM
        rw [Nat.eq_of_beq_eq_true hte]
      have e : T j = R m := by
        apply hφ
        rw [← hT, ← hR, heq]
      exact ⟨j, by omega, by rw [e]⟩
  have htgt : ∀ j < 28, T j ≠ 1 →
      3 ^ 7 ≤ Nat.card ↥(SylowPc.pcSub g 10 0 ⊓ Subgroup.centralizer ({T j} : Set G)) ∧
      ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({T j} : Set G) ∧ CFSG.Open.IsElemAbelian 3 E ∧
        Nat.card E = 9 ∧ ∀ x ∈ E, x ≠ 1 → IsConj x Z ∨ IsConj x (Z ^ 2) := by
    intro j hj hT1
    obtain ⟨t1, t2, t3, t4⟩ := tgtLocOK_dec (ch13650Tall j hj)
    set L := tc.getD j [] with hL
    set Ej := te.getD j [] with hEj
    set tn := permNfNum (tgts.getD j []) with htn
    have hLne : L ≠ [] := by
      intro e
      rw [e] at t1
      have e0 : tn = 0 := (Nat.eq_of_beq_eq_true t1).symm
      apply hT1
      change nfFrom g 10 0 tn = 1
      rw [e0, nfFrom_zero]
    obtain ⟨e0, he0, hh0⟩ := headN_mem_of_headL (Nat.eq_of_beq_eq_true t1) hLne
    let S : Set G := (fun e => nfFrom g 10 0 (headN e)) '' {e | e ∈ L}
    have hSfin : S.Finite := Set.toFinite S
    have hS27 : S.ncard ≤ 27 := by
      have e1 : {e | e ∈ L} = (L.toFinset : Set (List ℕ)) := by
        ext e
        simp
      calc S.ncard ≤ ({e | e ∈ L} : Set (List ℕ)).ncard := Set.ncard_image_le (by
            rw [e1]
            exact Finset.finite_toSet _)
        _ = L.toFinset.card := by rw [e1, Set.ncard_coe_finset]
        _ ≤ L.length := List.toFinset_card_le L
        _ ≤ 27 := by rw [← lenN_eq]; exact Nat.le_of_ble_eq_true t2
    have htS : T j ∈ S := by
      refine ⟨e0, he0, ?_⟩
      change nfFrom g 10 0 (headN e0) = nfFrom g 10 0 tn
      rw [hh0]
    have hcl : ∀ k < 10, ∀ y ∈ S, g k * y * (g k)⁻¹ ∈ S := by
      rintro k hk' _ ⟨e, he, rfl⟩
      obtain ⟨hlen, hrow⟩ := clsRows_spec L t3 e he
      have hl : (tailN e).length = 10 := by
        rw [tailN_length, ← lenN_eq, hlen]
      obtain ⟨hm, hk3⟩ := clsRow_spec (tailN e) 0 hrow k (by omega)
      obtain ⟨e', he', hh'⟩ := memH_spec L hm
      have ek := K3 hk3
      rw [Nat.zero_add, nfFrom_pow3 g hk'] at ek
      refine ⟨e', he', ?_⟩
      change nfFrom g 10 0 (headN e') = g k * nfFrom g 10 0 (headN e) * (g k)⁻¹
      rw [hh', ek]
      group
    have hcnt := card_inf_centralizer_ge g hSfin hS27 htS (nf_mem _) hcard hcl
    refine ⟨hcnt, ?_⟩
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ := e9OK_dec t4
    have hrecs := e9RecsOK_dec u6
    set x := nfFrom g 10 0 (Ej.getD 0 0) with hx
    set y := nfFrom g 10 0 (Ej.getD 1 0) with hy
    refine e9_facts (K3 u1) (K3 u2) (K3 u3) (C3 u4) (C3 u5) hZ1 hZ2 fun u hu => ?_
    have hu1 := u.1.isLt
    have hu2 := u.2.isLt
    have hpos : 0 < 3 * u.1.val + u.2.val := by
      rcases Nat.eq_zero_or_pos (3 * u.1.val + u.2.val) with h0 | h0
      · exfalso
        apply hu
        refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp <;> omega
      · exact h0
    set i := 3 * u.1.val + u.2.val - 1 with hi
    have hi8 : i < 8 := by omega
    have hd : (i + 1) / 3 = u.1.val := by omega
    have hm : (i + 1) % 3 = u.2.val := by omega
    have hr := hrecs i hi8
    rw [hd, hm] at hr
    set c := Ej.getD (2 + 2 * i) 0
    set f := Ej.getD (3 + 2 * i) 0
    obtain ⟨hz, k0, k1, k2⟩ := e9RecOK_dec hr
    have ec := e9Key_spec hstep hinj ho0' ho1' ho2' hsurj hmove k0 k1 k2
    have hcR : IsConj (pairP x y u) (nfFrom g 10 0 (zRep reps fus f)) := by
      refine isConj_iff.2 ⟨nfFrom g 10 0 c, ?_⟩
      change nfFrom g 10 0 c * (x ^ u.1.val * y ^ u.2.val) * (nfFrom g 10 0 c)⁻¹ = _
      rw [ec]
      group
    obtain ⟨hf52', hzz⟩ := zRepOK_dec hz
    by_cases hf50 : f = 50
    · left
      have e : zRep reps fus f = 19683 := by rw [hf50]; rfl
      rw [e, hz9] at hcR
      exact hcR
    by_cases hf51 : f = 51
    · right
      have e : zRep reps fus f = 39366 := by rw [hf51]; rfl
      rw [e, hz92] at hcR
      exact hcR
    have hf : f < 50 := by omega
    rw [zRep_of_lt hf] at hcR
    have hzt : isZ (permNfNum (tgts.getD ((fus.getD f []).getD 1 0) [])) = true := by
      rcases hzz with h5 | h5
      · omega
      · exact h5
    obtain ⟨hcf, -⟩ := hfus f hf
    have hc2 : IsConj (pairP x y u)
        (nfFrom g 10 0 (permNfNum (tgts.getD ((fus.getD f []).getD 1 0) []))) := hcR.trans hcf
    rcases isZ_dec hzt with h5 | h5
    · left
      rw [h5, hz9] at hc2
      exact hc2
    · right
      rw [h5, hz92] at hc2
      exact hc2
  refine ⟨SylowPc.pcSub g 10 0, hcard, hZQ, hZ3, hcent, hinv, fun s hs ho => ?_⟩
  have hs3 : s ^ 3 = 1 := by rw [← ho]; exact pow_orderOf_eq_one s
  rw [hnr] at hconjQ
  rcases hconjQ s hs hs3 with h1 | ⟨m, hm, c, -, hc⟩
  · rw [h1, orderOf_one] at ho
    exact absurd ho (by norm_num)
  obtain ⟨j, hj, hRT⟩ := hrt m hm
  have hsR : IsConj s (R m) := isConj_iff.2 ⟨c, hc⟩
  have hsT := hsR.trans hRT
  have hT1 : T j ≠ 1 := by
    intro h1
    rw [h1, isConj_one_left] at hsT
    rw [hsT, orderOf_one] at ho
    exact absurd ho (by norm_num)
  exact ⟨T j, hsT, htgt j hj hT1⟩

end Facts

end CertificateChecks.KernelThLocal

end
