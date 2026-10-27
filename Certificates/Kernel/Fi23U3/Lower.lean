module

public import Certificates.Kernel.Fi23U3.Chain
public import Certificates.Kernel.Fi23U3.Rels
public import CFSG.Certificates.Kernel.LaneChainSound
public import CFSG.Certificates.Kernel.OpsRenLSound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3Sound
import CFSG.Certificates.Kernel.Spor.OrdCanon
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFi23U3

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.KC.OpsLayK.Snd CFSG.KS.Ord CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CertificateChecks.KernelTc.Fi23
  CFSG.KC.LocalComp.Ops3Snd CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
  CFSG.KC.LayWords

instance fi23U3_m_neZero : NeZero fi23U3Cover3.m := ⟨by decide⟩

noncomputable abbrev SM : Submonoid (Matrix (Fin 253) (Fin 253) (ZMod 3)) :=
  CFSG.Blueprint.NativeSporadic.seedMonoid 3 253 1 fi23U3Cover3.seedA fi23U3Cover3.seedB

section Closure

variable {c : Lay} {P : Nat → Prop} (h1 : P c.ONE) (hm : ∀ x y, P x → P y → P (c.mul x y))
include h1 hm

theorem powN_P : ∀ (f X e : Nat), P X → P (powN c f X e)
  | 0, _, _, _ => h1
  | f + 1, X, e, hX => by
    have ih := powN_P f (c.mul X X) (Nat.div e 2) (hm X X hX hX)
    change P (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (CFSG.KC.Loop.strictN (c.mul X X) fun X2 =>
          CFSG.KC.Loop.strictN (powN c f X2 (Nat.div e 2)) fun Y =>
            Bool.rec (motive := fun _ => Nat) Y (c.mul X Y) (Nat.beq (Nat.mod e 2) 1))
        X (Nat.beq e 1))
      c.ONE (Nat.beq e 0))
    simp only [CFSG.KS.LaneChain.strictN_app]
    cases Nat.beq e 0 <;> cases Nat.beq e 1 <;> cases Nat.beq (Nat.mod e 2) 1 <;>
      first | exact h1 | exact hX | exact ih | exact hm _ _ hX ih

omit hm in
theorem getR_P {R : List Nat} (hR : ∀ x ∈ R, P x) (i : Nat) : P (getR c R i) := by
  unfold getR
  rw [List.getD_eq_getElem?_getD]
  cases h : R[i]? with
  | none => exact h1
  | some x => exact hR x (List.mem_of_getElem? h)

theorem runL_P : ∀ (prog : List Op) (R : List Nat), (∀ i, P (getR c R i)) →
    ∀ i, P (getR c (runL c prog R) i)
  | [], _, hR => hR
  | o :: prog, R, hR => by
    have hv : P (stepV c R o) := by
      cases o with
      | mul i j k => exact hm _ _ (hR i) (hR j)
      | pow e i k => exact powN_P h1 hm 17 _ e (hR i)
    refine runL_P prog (R.set (Op.tgt o) (stepV c R o)) fun i => ?_
    by_cases hti : Op.tgt o = i
    · subst hti
      by_cases ht : Op.tgt o < R.length
      · rw [getR_set_self c _ ht]
        exact hv
      · rw [List.set_eq_of_length_le (by omega)]
        exact hR _
    · rw [getR_set_ne c _ hti]
      exact hR i

theorem chunkV_P {ch : RChunk} {S S' : List Nat} (hS : ∀ x ∈ S, P x)
    (h : chunkV c ch S S' = true) : ∀ x ∈ S', P x := by
  unfold chunkV at h
  rw [runC_eq] at h
  rw [← eq_of_eqL h]
  intro x hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  refine runL_P h1 hm _ _ (getR_P h1 fun y hy => ?_) r
  unfold padR at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact hS y hy
  · rw [List.eq_of_mem_replicate hy]
    exact h1

end Closure

theorem prog_length : prog.length ≤ 5 * 50 := by decide

theorem prog_ok : progOK 25 prog = true := by decide

theorem RF_eq : runL lay prog (initR lay A B 25) = RF := by
  rw [← eq_of_eqL init]
  exact runL_of_chunks (S := fun i => S.SL.getD i []) prog_length ch_all

theorem RF_length : RF.length = 25 := by
  rw [← RF_eq, runL_initR_length]

theorem hsA : fi23U3Cover3.seedA = String.ofList LA :=
  (rfl : fi23U3Cover3.seedA = CFSG.Blueprint.NativeSporadic.Fi23Seed1).trans LA_eq

theorem hsB : fi23U3Cover3.seedB = String.ofList LB :=
  (rfl : fi23U3Cover3.seedB = CFSG.Blueprint.NativeSporadic.Fi23Seed2).trans LB_eq

theorem RF_mem {r : Nat} (hr : r < 25) :
    Canon lay.p lay.d lay.w (getR lay RF r) ∧ mat3 lay (getR lay RF r) ∈ SM := by
  have hL := lcorr_regs lay_ok rfl decA decB hsA hsB prog_ok
  rw [RF_eq] at hL
  obtain ⟨hc, -, hmat⟩ := hL.2 r (by rw [RF_length]; exact hr)
  obtain ⟨-, hS⟩ := (spec3b lay.d).regsOf_ok (seedA := fi23U3Cover3.seedA)
    (seedB := fi23U3Cover3.seedB) (progOK_spec prog_ok).2 hr
  refine ⟨hc, ?_⟩
  rw [← hmat]
  exact hS

theorem X_mem {i : Nat} (hi : i < 4) :
    Canon lay.p lay.d lay.w (X i) ∧ mat3 lay (X i) ∈ SM :=
  RF_mem (by interval_cases i <;> decide)

theorem codesInv_cons (a : Nat) (w : List Nat) :
    codesInv lay X (a :: w) = lay.mul (X (a / 2)) (codesInv lay X w) := by
  change CFSG.KC.Loop.strictN (codesInv lay X w)
    (fun y => lay.mul (X (Nat.shiftRight a 1)) y) = _
  rw [CFSG.KS.LaneChain.strictN_app]
  have e : Nat.shiftRight a 1 = a / 2 := (Nat.shiftRight_eq_div_pow a 1).trans (by norm_num)
  rw [e]

theorem codes_mat : ∀ w : List Nat, (∀ a ∈ w, a / 2 < 4) →
    Canon lay.p lay.d lay.w (codesInv lay X w) ∧
      mat3 lay (codesInv lay X w) = (w.map fun a => mat3 lay (X (a / 2))).prod
  | [], _ => by
    refine ⟨(mat3_one lay lay_ok rfl).1, ?_⟩
    rw [List.map_nil, List.prod_nil]
    exact (mat3_one lay lay_ok rfl).2
  | a :: w, h => by
    obtain ⟨c1, m1⟩ := codes_mat w fun b hb => h b (List.mem_cons_of_mem _ hb)
    obtain ⟨c0, -⟩ := X_mem (h a List.mem_cons_self)
    obtain ⟨c2, m2⟩ := mat3_mul lay lay_ok rfl c0 c1
    rw [codesInv_cons]
    exact ⟨c2, by rw [m2, m1, List.map_cons, List.prod_cons]⟩

theorem codes_one {w : List Nat} (hw : ∀ a ∈ w, a / 2 < 4) (h : codesOneInv lay X w = true) :
    (w.map fun a => mat3 lay (X (a / 2))).prod = 1 := by
  rw [← (codes_mat w hw).2, Nat.eq_of_beq_eq_true h]
  exact (mat3_one lay lay_ok rfl).2

theorem X_sq {i : Nat} (hi : i < 4) : mat3 lay (X i) ^ 2 = 1 := by
  have h := codes_one (w := [2 * i, 2 * i]) (by simp; omega) (sq_all i hi)
  simpa [pow_two, Nat.mul_div_cancel_left i (by norm_num : 0 < 2)] using h

noncomputable def gU (i : Fin fi23U3Cover3.m) : SMˣ :=
  unitOf SM (X_mem (i := i.val) i.isLt).2 two_ne_zero (X_sq (i := i.val) i.isLt)

theorem val_gU (i : Fin fi23U3Cover3.m) : valHom SM (gU i) = mat3 lay (X i.val) :=
  valHom_unitOf _ _ _ _

theorem gU_sq (i : Fin fi23U3Cover3.m) : gU i ^ 2 = 1 := unitOf_pow _ _ _ _

theorem gU_inv (i : Fin fi23U3Cover3.m) : (gU i)⁻¹ = gU i := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, gU_sq]

theorem lift_codes : ∀ w : List Nat, (∀ a ∈ w, a / 2 < 4) →
    valHom SM (FreeGroup.lift gU (FreeGroup.mk (ofCodes fi23U3Cover3.m w))) =
      (w.map fun a => mat3 lay (X (a / 2))).prod
  | [], _ => by
    change valHom SM (FreeGroup.lift gU 1) = (1 : Matrix (Fin 253) (Fin 253) (ZMod 3))
    rw [map_one, map_one]
  | a :: w, h => by
    have ha : a / 2 < 4 := h a List.mem_cons_self
    have e : FreeGroup.mk (ofCodes fi23U3Cover3.m (a :: w)) =
        FreeGroup.mk [(Fin.ofNat fi23U3Cover3.m (a / 2), decide (a % 2 = 0))] *
          FreeGroup.mk (ofCodes fi23U3Cover3.m w) := by
      rw [FreeGroup.mul_mk]
      rfl
    have hg : FreeGroup.lift gU
        (FreeGroup.mk [(Fin.ofNat fi23U3Cover3.m (a / 2), decide (a % 2 = 0))]) =
          gU (Fin.ofNat fi23U3Cover3.m (a / 2)) := by
      cases decide (a % 2 = 0)
      · rw [show FreeGroup.mk [(Fin.ofNat fi23U3Cover3.m (a / 2), false)] =
          (FreeGroup.of (Fin.ofNat fi23U3Cover3.m (a / 2)))⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of, gU_inv]
      · rw [show FreeGroup.mk [(Fin.ofNat fi23U3Cover3.m (a / 2), true)] =
          FreeGroup.of (Fin.ofNat fi23U3Cover3.m (a / 2)) from rfl, FreeGroup.lift_apply_of]
    have hv : (Fin.ofNat fi23U3Cover3.m (a / 2)).val = a / 2 := by
      rw [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt ha
    rw [e, map_mul, hg, map_mul, val_gU, hv,
      lift_codes w fun b hb => h b (List.mem_cons_of_mem _ hb), List.map_cons, List.prod_cons]
    rfl

theorem relCodes_lt : (fi23U3Cover3.relCodes.all fun r => r.all fun a => decide (a / 2 < 4)) =
    true := by
  decide

theorem rels_one : ∀ r ∈ fi23U3Cover3.rels, FreeGroup.lift gU (FreeGroup.mk r) = 1 := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hw : ∀ a ∈ fi23U3Cover3.relCodes[j], a / 2 < 4 := fun a ha =>
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 relCodes_lt _ hc) a ha)
  have h : codesOneInv lay X (fi23U3Cover3.relCodes.getD j []) = true :=
    rel_all j (lt_of_lt_of_eq hj rels_length)
  rw [List.getD_eq_getElem _ _ hj] at h
  apply valHom_injective SM
  rw [lift_codes _ hw, map_one, codes_one hw h]
  rfl

noncomputable abbrev U : Subgroup SMˣ := Subgroup.closure (Set.range gU)

abbrev GoodU (x : Nat) : Prop :=
  CFSG.KS.LaneChain.Good (valHom SM) U lay.w lay.S (lay.d * lay.S) lay.L lay.H x

theorem good_one : GoodU lay.ONE := by
  obtain ⟨h1, h2⟩ := CFSG.KS.J4Hub.one_sound' (p := 3) (d := 253) lay_ok rfl
  exact ⟨h1, 1, U.one_mem, by rw [map_one]; exact h2⟩

theorem good_mul (x y : Nat) (hx : GoodU x) (hy : GoodU y) : GoodU (lay.mul x y) :=
  CFSG.KS.LaneChain.good_mul (valHom SM) U lay_ok rfl hx hy

theorem good_X {i : Nat} (hi : i < 4) : GoodU (X i) := by
  have hc := (X_mem hi).1
  refine ⟨CFSG.KS.OrdCanon.validM_of_canon lay_ok hc, gU ⟨i, hi⟩,
    Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩, ?_⟩
  exact (val_gU ⟨i, hi⟩).symm

theorem good_Q1 : ∀ x ∈ Q.SL.getD 1 [], GoodU x := by
  have h : chunkV lay (25, [], [16, 19, 22, 4]) (Q.SL.getD 0 []) (Q.SL.getD 1 []) = true :=
    rc_all 0 (by norm_num)
  unfold chunkV at h
  rw [runC_eq] at h
  rw [← eq_of_eqL h]
  have hq : Q.SL.getD 0 [] = RF := q0_eq
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  have hr25 : r < (Q.SL.getD 0 []).length := by
    rw [hq, RF_length]
    simp at hr
    omega
  change GoodU (getR lay (padR lay (Q.SL.getD 0 []) 25) r)
  rw [getR_padR lay 25 hr25, hq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact good_X (i := 0) (by norm_num)
  · exact good_X (i := 1) (by norm_num)
  · exact good_X (i := 2) (by norm_num)
  · exact good_X (i := 3) (by norm_num)

theorem good_Q4 : ∀ x ∈ Q.SL.getD 4 [], GoodU x :=
  chunkV_P good_one good_mul
    (chunkV_P good_one good_mul (chunkV_P good_one good_mul good_Q1 (rc_all 1 (by norm_num)))
      (rc_all 2 (by norm_num)))
    (rc_all 3 (by norm_num))

theorem allGood_M₀ : CFSG.KS.LaneChain.AllGood (valHom SM) U lay.w lay.S (lay.d * lay.S) lay.L
    lay.H M₀ := fun _ hr =>
  good_Q4 _ (List.mem_reverse.1 (CFSG.KS.LaneChain.getR_mem hr))

theorem card_ge : 6377292 ≤ Nat.card U :=
  CFSG.KS.LaneChain.card_ge_of_chainOK (valHom SM) U lay_ok rfl allGood_M₀ chain_ok

theorem lower_facts :
    ∃ g : Fin fi23U3Cover3.m →
        (CFSG.Blueprint.NativeSporadic.seedMonoid 3 253 1 fi23U3Cover3.seedA fi23U3Cover3.seedB)ˣ,
      (∀ r ∈ fi23U3Cover3.rels, FreeGroup.lift g (FreeGroup.mk r) = 1) ∧ (∀ i, g i ^ 2 = 1) ∧
      6377292 ≤ Nat.card (Subgroup.closure (Set.range g)) :=
  ⟨gU, rels_one, gU_sq, card_ge⟩

end CertificateChecks.KernelFi23U3

end
