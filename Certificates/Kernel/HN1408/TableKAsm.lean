module

public import Certificates.Kernel.HN1408.TableKShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKFacts
public import Certificates.Kernel.HN1408.CzTScan

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TK

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KC.BfsPin CFSG.KC.Blk CFSG.KD.HN1408 CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HNRecog.HaradaModel

abbrev Nk : Subgroup (Equiv.Perm (Fin 1408)) := Zk ⊔ Qk

theorem Z_gens : ∀ s ∈ elemW '' {w | w ∈ zcWordsK}, s = elemW xWordK ∨ s = elemW yWordK := by
  rintro _ ⟨w, hw, rfl⟩
  simp only [zcWordsK, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hw
  rcases hw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem N_eq : Nk = closure (elemW '' {w | w ∈ zcWordsK} ∪ elemW '' {w | w ∈ qWordsK}) :=
  (Subgroup.closure_union _ _).symm

theorem Z_comm_N : ∀ z ∈ Zk, ∀ n ∈ Nk, z * n = n * z := by
  rw [N_eq]
  refine commute_of_closure ?_
  obtain ⟨-, -, -, hxy, hq⟩ := zc_facts
  intro s hs t ht
  rcases ht with ht | ht
  · rcases Z_gens s hs with rfl | rfl <;> rcases Z_gens t ht with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  · revert t
    refine of_gens (k := 4) (by decide) fun j hj => ?_
    rcases Z_gens s hs with rfl | rfl
    · exact (hq j hj).1
    · exact (hq j hj).2

theorem Z_comm_Q : ∀ z ∈ Zk, ∀ q ∈ Qk, z * q = q * z :=
  fun z hz q hq => Z_comm_N z hz q (le_sup_right (a := Zk) hq)

theorem join : ∀ n ∈ Nk, ∃ z ∈ Zk, z⁻¹ * n ∈ Qk := by
  let J : Subgroup (Equiv.Perm (Fin 1408)) :=
    { carrier := {n | ∃ z ∈ Zk, z⁻¹ * n ∈ Qk}
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul]; exact one_mem _⟩
      mul_mem' := by
        rintro a b ⟨z1, hz1, hq1⟩ ⟨z2, hz2, hq2⟩
        obtain ⟨q1, hq1', rfl⟩ : ∃ q ∈ Qk, a = z1 * q := ⟨z1⁻¹ * a, hq1, by group⟩
        obtain ⟨q2, hq2', rfl⟩ : ∃ q ∈ Qk, b = z2 * q := ⟨z2⁻¹ * b, hq2, by group⟩
        refine ⟨z1 * z2, mul_mem hz1 hz2, ?_⟩
        have h := Z_comm_Q z2 hz2 q1 hq1'
        have e : (z1 * z2)⁻¹ * (z1 * q1 * (z2 * q2)) = q1 * q2 := by
          calc (z1 * z2)⁻¹ * (z1 * q1 * (z2 * q2)) = z2⁻¹ * (q1 * z2) * q2 := by group
            _ = z2⁻¹ * (z2 * q1) * q2 := by rw [h]
            _ = q1 * q2 := by group
        rw [e]
        exact mul_mem hq1' hq2'
      inv_mem' := by
        rintro a ⟨z, hz, hq⟩
        obtain ⟨q, hq', rfl⟩ : ∃ q ∈ Qk, a = z * q := ⟨z⁻¹ * a, hq, by group⟩
        refine ⟨z⁻¹, inv_mem hz, ?_⟩
        have h := Z_comm_Q z hz q⁻¹ (inv_mem hq')
        have e : z⁻¹⁻¹ * (z * q)⁻¹ = q⁻¹ := by
          calc z⁻¹⁻¹ * (z * q)⁻¹ = z * q⁻¹ * z⁻¹ := by group
            _ = q⁻¹ * z * z⁻¹ := by rw [h]
            _ = q⁻¹ := by group
        rw [e]
        exact inv_mem hq' }
  have hle : Nk ≤ J := sup_le (fun z hz => ⟨z, hz, by rw [inv_mul_cancel]; exact one_mem _⟩)
    (fun q hq => ⟨1, one_mem _, by rw [inv_one, one_mul]; exact hq⟩)
  exact fun n hn => hle hn

theorem N_cen : ∀ n ∈ Nk, (∀ m ∈ Nk, n * m = m * n) → n ∈ Zk := by
  intro n hn hc
  obtain ⟨z, hz, hq⟩ := join n hn
  have hcen : ∀ r ∈ Qk, (z⁻¹ * n) * r = r * (z⁻¹ * n) := by
    intro r hr
    have h1 := hc r (le_sup_right (a := Zk) hr)
    have h2 := Z_comm_Q z⁻¹ (inv_mem hz) r hr
    calc z⁻¹ * n * r = z⁻¹ * (n * r) := by group
      _ = z⁻¹ * (r * n) := by rw [h1]
      _ = (z⁻¹ * r) * n := by group
      _ = (r * z⁻¹) * n := by rw [h2]
      _ = r * (z⁻¹ * n) := by group
  have e : n = z * (z⁻¹ * n) := by group
  rcases Q_cen _ hq hcen with h | h
  · rw [e, h, mul_one]
    exact hz
  · rw [e, h]
    exact mul_mem hz c_mem_Z

theorem card_N_ge : 128 ≤ Nat.card ↥Nk := by
  classical
  have hcomm : ∀ (a : ↥Zk) (b : ↥Qk), Commute (Zk.subtype a) (Qk.subtype b) :=
    fun a b => Z_comm_Q a.1 a.2 b.1 b.2
  let μ := MonoidHom.noncommCoprod Zk.subtype Qk.subtype hcomm
  have hrange : μ.range ≤ Nk := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change (a : Equiv.Perm (Fin 1408)) * b ∈ Nk
    exact mul_mem (le_sup_left (b := Qk) a.2) (le_sup_right (a := Zk) b.2)
  have hk : ∀ k : ↥μ.ker, ((k : ↥Zk × ↥Qk).2 : Equiv.Perm (Fin 1408)) =
      ((k : ↥Zk × ↥Qk).1 : Equiv.Perm (Fin 1408))⁻¹ ∧
      (((k : ↥Zk × ↥Qk).1 : Equiv.Perm (Fin 1408)) = 1 ∨
        ((k : ↥Zk × ↥Qk).1 : Equiv.Perm (Fin 1408)) = elemW cWordK) := by
    rintro ⟨⟨a, b⟩, hab⟩
    have e : (a : Equiv.Perm (Fin 1408)) * b = 1 := MonoidHom.mem_ker.1 hab
    have ha : (a : Equiv.Perm (Fin 1408)) = (b : Equiv.Perm (Fin 1408))⁻¹ :=
      eq_inv_of_mul_eq_one_left e
    refine ⟨eq_inv_of_mul_eq_one_right e, Q_cen _ ?_ fun r hr => Z_comm_Q a.1 a.2 r hr⟩
    rw [ha]
    exact inv_mem b.2
  let f : ↥μ.ker → Bool := fun k => decide (((k : ↥Zk × ↥Qk).1 : Equiv.Perm (Fin 1408)) = 1)
  have hf : Function.Injective f := by
    intro k1 k2 h12
    obtain ⟨q1, c1⟩ := hk k1
    obtain ⟨q2, c2⟩ := hk k2
    have e1 : ((k1 : ↥Zk × ↥Qk).1 : Equiv.Perm (Fin 1408)) = (k2 : ↥Zk × ↥Qk).1 := by
      simp only [f] at h12
      rcases c1 with h1 | h1 <;> rcases c2 with h2 | h2
      · rw [h1, h2]
      · rw [h1, h2] at h12
        simp [c_ne] at h12
      · rw [h1, h2] at h12
        simp [c_ne] at h12
      · rw [h1, h2]
    exact Subtype.ext (Prod.ext (Subtype.ext e1) (Subtype.ext (by rw [q1, q2, e1])))
  have hker : Nat.card ↥μ.ker ≤ 2 := by
    calc Nat.card ↥μ.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  have hprod : Nat.card (↥Zk × ↥Qk) = 256 := by rw [Nat.card_prod, card_Z, card_Q]
  have h := Subgroup.card_ker_mul_card_range μ
  rw [hprod] at h
  have hle := Subgroup.card_le_of_le hrange
  have hr : 128 ≤ Nat.card ↥μ.range := by nlinarith
  omega

theorem triv_of {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g)
    (h : blkTrivK 1408 11 4 (TB.F 0) X = true) :
    ∀ p : Fin 1408, blkF 5 blkData1.blk (g p) = blkF 5 blkData1.blk p := by
  have h' : blkTrivOK blkData1.blk (tabT (unpack 1408 11 X)) = true := by
    rw [blk1, blkTrivOK_eq hX.1]
    exact h
  exact blkTrivOK_spec hX.2 h'

theorem blk_parts : (∀ j < 2, blkTrivK 1408 11 4 (TB.F 0) (TKZ.GI j) = true) ∧
    ∀ j < 4, blkTrivK 1408 11 4 (TB.F 0) (TKQ.GI j) = true := by
  have h := ch26773_blk
  simp only [bAnd_iff] at h
  exact ⟨fun j hj => allN_spec h.1 j hj, fun j hj => allN_spec h.2 j hj⟩

theorem N_triv : ∀ n ∈ Nk, ∀ p : Fin 1408, blkF 5 blkData1.blk (n p) = blkF 5 blkData1.blk p := by
  rw [N_eq]
  refine blkTriv_closure_set ?_
  rintro t (ht | ht)
  · revert t
    exact of_gens (k := 2) (by decide) fun j hj =>
      triv_of (gen_of lZ hdZ j hj) (blk_parts.1 j hj)
  · revert t
    exact of_gens (k := 4) (by decide) fun j hj =>
      triv_of (gen_of lQ hdQ j hj) (blk_parts.2 j hj)

theorem kW_le : closure (elemW '' {w | w ∈ kWords}) ≤ czC ⊓ blocks1408 := by
  rw [closure_le]
  refine of_gens (k := 3) (by decide) fun l hl => ⟨?_, ?_⟩
  · exact closure_specWords_le classz.centGens kSpec (elemW_getD_mem kWords l)
  · exact pres_of (by rw [kK_eq]; exact repC_word (lettersOK_getD lK l)) (half_parts.1 l hl)

theorem N_le : Nk ≤ czC ⊓ blocks1408 := by
  have hnk : closure (elemW '' {w | w ∈ nWordsK}) ≤ closure (elemW '' {w | w ∈ kWords}) :=
    closure_specWords_le kWords nSpecK
  have hZ : Zk ≤ closure (elemW '' {w | w ∈ nWordsK}) := by
    rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [zcWordsK, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hw
    rcases hw with rfl | rfl
    · exact elemW_specWord_mem nWordsK xSpecK
    · exact elemW_specWord_mem nWordsK ySpecK
  have hQ : Qk ≤ closure (elemW '' {w | w ∈ nWordsK}) := closure_specWords_le nWordsK qSpecK
  exact sup_le (hZ.trans (hnk.trans kW_le)) (hQ.trans (hnk.trans kW_le))

theorem tableKFacts (hP : Nat.card ↥P1408 = 177408000) : TableKFacts := by
  obtain ⟨hCeq, -⟩ := czT_eq hP
  have hK : kSub1408 = czC ⊓ blocks1408 := by rw [hCeq]
  obtain ⟨φC, hrC, hkC⟩ := blkC
  have hKC : czC ⊓ blocks1408 ≤ czC := inf_le_left
  let φ : ↥(czC ⊓ blocks1408) →* Equiv.Perm (Fin 5) := φC.comp (Subgroup.inclusion hKC)
  have hNker : ∀ (n : Equiv.Perm (Fin 1408)) (h : n ∈ Nk), φ ⟨n, N_le h⟩ = 1 := by
    intro n h
    change φC ⟨n, hKC (N_le h)⟩ = 1
    rw [hkC]
    exact N_triv n h
  have hrange : Nat.card ↥φ.range = 120 := by
    have e : φ.range = φC.range := by
      apply le_antisymm
      · rintro _ ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      · rintro _ ⟨g, rfl⟩
        have hg2 : (g : Equiv.Perm (Fin 1408)) ∈ blocks1408 ∨ SwH g := czC_dich g.2
        rcases hg2 with hb | hb
        · exact ⟨⟨g.1, g.2, hb⟩, rfl⟩
        · refine ⟨⟨g.1 * elemW (specWord classz.centGens (nSpec1.getD 3 [])),
            mul_mem g.2 n_mem, swH_mul_swH hb n_swH⟩, ?_⟩
          have hn1 : φC ⟨_, n_mem⟩ = 1 := (hkC _).2 n_triv
          change φC (g * ⟨_, n_mem⟩) = φC g
          rw [map_mul, hn1, mul_one]
    rw [e]
    exact hrC
  have hNle : Nat.card ↥Nk ≤ 128 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [card_K' hP, hrange] at h1
    have hk : Nat.card ↥φ.ker = 128 := by omega
    have hle : Nk.subgroupOf (czC ⊓ blocks1408) ≤ φ.ker := fun x hx => by
      rw [MonoidHom.mem_ker]
      exact hNker x.1 (Subgroup.mem_subgroupOf.1 hx)
    have h2 := Subgroup.card_le_of_le hle
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le).toEquiv] at h2
    omega
  have hN : Nat.card ↥Nk = 128 := le_antisymm hNle card_N_ge
  obtain ⟨hxo, hyo, hyn, -, -⟩ := zc_facts
  have hQcomm : ∀ q ∈ Qk, ∀ r ∈ Qk,
      q * r * (r * q)⁻¹ = 1 ∨ q * r * (r * q)⁻¹ = elemW cWordK := by
    intro q hq r hr
    rcases Q_comm q hq r hr with h | h
    · left
      rw [h, mul_inv_cancel]
    · right
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨?_, ?_⟩
  · rw [hK]
    exact TwoHSData.isShapeK_of_data _ Nk Zk Qk Ek (elemW xWordK) (elemW yWordK) (elemW cWordK) φ
      N_le hNker (card_K' hP) hN hrange le_sup_left Z_comm_N N_cen card_Z
      (subset_closure ⟨xWordK, by simp [zcWordsK], rfl⟩)
      (subset_closure ⟨yWordK, by simp [zcWordsK], rfl⟩) hxo hyo hyn le_sup_right card_Q c_mem_Q
      c_mem_Z c_ne c_sq Q_cen hQcomm Q_sq E_le_Q E_comm E_sq card_E join
  · rw [hK]
    intro y hy hc
    have hyC : y ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
      rw [← hCeq]
      exact hy.1
    obtain ⟨c0, c1, c2, -, -⟩ := ctK_parts czT_ct
    have htK : ∀ l < 3, elemW (tGens.getD l []) ∈ czC ⊓ blocks1408 := by
      intro l hl
      have hr := repC_word (tGens_letters hl)
      refine ⟨?_, pres_of hr (half_parts.2.1 l hl)⟩
      rw [hCeq]
      refine mem_cent_of hr (elemW_mem _) ?_
      interval_cases l
      · exact c0
      · exact c1
      · exact c2
    have h3 : tGens.length = 3 := by decide
    rcases cent_tGens hP hyC (fun w hw => by
        obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hw
        rw [← List.getD_eq_getElem _ [] hl]
        exact hc _ (htK l (h3 ▸ hl))) with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ rfl))

end CFSG.KD.HN1408.TK

end
