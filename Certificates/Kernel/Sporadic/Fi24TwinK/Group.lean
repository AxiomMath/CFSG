module

public import Certificates.Kernel.Sporadic.Fi24TwinK.Facts
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group
public import Certificates.Kernel.Sporadic.Fi24ThreeAK.Facts
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24TwinFacts

public section

namespace CFSG.KD.Fi24TwinK.Group

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.HardMathSupport.Dickson.I271
open CFSG.Sporadic.Fi24 (R J jR tR cls gs letters)
open CFSG.Perm CFSG.KC CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO CFSG.KC.Fi24TwinK CFSG.KS.Fi24ThreeO
  CFSG.KS.Fi24TwinK CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO.Group

attribute [local instance] CFSG.Sporadic.Fi24.rAction

open scoped commutatorElement

section ClassTwo

variable {G : Type*} [Group G]

theorem triple_comm_closure (X : Set G)
    (hX : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, Commute (x⁻¹ * y⁻¹ * x * y) z) :
    ∀ a ∈ Subgroup.closure X, ∀ b ∈ Subgroup.closure X, ∀ c ∈ Subgroup.closure X,
      ⁅⁅a, b⁆, c⁆ = 1 := by
  set K := Subgroup.closure X
  set Z := Subgroup.centralizer (K : Set G)
  have cen : ∀ g, (∀ z ∈ X, Commute g z) → g ∈ Z := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem z hz => exact (hg z hz).eq.symm
    | one => rw [one_mul, mul_one]
    | mul u v _ _ hu hv => rw [mul_assoc, hv, ← mul_assoc, hu, mul_assoc]
    | inv u _ hu =>
      calc u⁻¹ * g = u⁻¹ * (g * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * g) * u⁻¹ := by rw [hu]
        _ = g * u⁻¹ := by group
  have zc : ∀ g ∈ Z, ∀ k ∈ K, k * g * k⁻¹ = g := fun g hg k hk => by
    rw [Subgroup.mem_centralizer_iff.1 hg k hk, mul_inv_cancel_right]
  have h1 : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ Z := by
    intro x hx y hy
    have hc : x⁻¹ * y⁻¹ * x * y ∈ Z := cen _ (hX x hx y hy)
    have e : ⁅x, y⁆ = (x * y) * (x⁻¹ * y⁻¹ * x * y) * (x * y)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e, zc _ hc _ (K.mul_mem (Subgroup.subset_closure hx) (Subgroup.subset_closure hy))]
    exact hc
  have h2 : ∀ a ∈ K, ∀ y ∈ X, ⁅a, y⁆ ∈ Z := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact h1 x hx
    | one => intro y _; rw [commutatorElement_one_left]; exact Z.one_mem
    | mul u v hu' hv' hu hv =>
      intro y hy
      have e : ⁅u * v, y⁆ = u * ⁅v, y⁆ * u⁻¹ * ⁅u, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e, zc _ (hv y hy) u hu']
      exact Z.mul_mem (hv y hy) (hu y hy)
    | inv u hu' hu =>
      intro y hy
      have e : ⁅u⁻¹, y⁆ = u⁻¹ * ⁅u, y⁆⁻¹ * u⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, zc _ (Z.inv_mem (hu y hy)) u⁻¹ (K.inv_mem hu')]
      exact Z.inv_mem (hu y hy)
  have h3 : ∀ b ∈ K, ∀ a ∈ K, ⁅a, b⁆ ∈ Z := by
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem y hy => exact fun a ha => h2 a ha y hy
    | one => intro a _; rw [commutatorElement_one_right]; exact Z.one_mem
    | mul u v hu' hv' hu hv =>
      intro a ha
      have e : ⁅a, u * v⁆ = ⁅a, u⁆ * (u * ⁅a, v⁆ * u⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e, zc _ (hv a ha) u hu']
      exact Z.mul_mem (hu a ha) (hv a ha)
    | inv u hu' hu =>
      intro a ha
      have e : ⁅a, u⁻¹⁆ = u⁻¹ * ⁅a, u⁆⁻¹ * u⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, zc _ (Z.inv_mem (hu a ha)) u⁻¹ (K.inv_mem hu')]
      exact Z.inv_mem (hu a ha)
  intro a ha b hb c hc
  have hz := h3 b hb a ha
  rw [commutatorElement_def, ← Subgroup.mem_centralizer_iff.1 hz c hc, mul_inv_cancel_right,
    mul_inv_cancel]

end ClassTwo

section Setup

@[expose] def pf (n : ℕ) : Fin 306936 := ⟨n % 306936, Nat.mod_lt _ (by norm_num)⟩

theorem pf_val {n : ℕ} (h : n < 306936) : (pf n).val = n := Nat.mod_eq_of_lt h

theorem pf_of (a : Fin 306936) : pf a.val = a := Fin.ext (pf_val a.2)

theorem root_eq : CFSG.Sporadic.Fi24.root = pf 0 := rfl

theorem wr_lt : ∀ r < 3, ∀ l ∈ wr r, l < 26 := by decide +kernel

@[expose] noncomputable def xr (r : ℕ) : R := jR (wordElt (wr r))

theorem cls_inv (k : Fin 306936) : (cls k)⁻¹ = cls k :=
  inv_eq_of_mul_eq_one_right (cls_mul_self k)

theorem hconj : ∀ (g : R) (i : Fin 306936), cls (g • i) = g * cls i * g⁻¹ :=
  CFSG.Sporadic.Fi24.cls_smul_R

variable (hB : Bridge) {r : ℕ} (hT : TwinN r)
include hB hT

theorem pt_lt {i : ℕ} (hi : i < m r) : pt (F r) i < 306936 :=
  ((hT.fix _).2 ⟨i, hi, rfl⟩).1

theorem pt_inj {i j : ℕ} (hi : i < m r) (hj : j < m r) (h : pt (F r) i = pt (F r) j) : i = j := by
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd h (Nat.ne_of_lt (hT.inc i j h' hj))
  · exact h'
  · exact absurd h.symm (Nat.ne_of_lt (hT.inc j i h' hi))

theorem fix_iff (hr : r < 3) (a : Fin 306936) :
    xr r • a = a ↔ ∃ i < m r, pt (F r) i = a.val := by
  unfold xr
  rw [CFSG.Sporadic.Fi24.jR_smul, ← (hT.fix a.val), ← word_val hB (wr r) (wr_lt r hr) a,
    Fin.val_eq_val]
  exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

theorem pf_fix (hr : r < 3) {i : ℕ} (hi : i < m r) : xr r • pf (pt (F r) i) = pf (pt (F r) i) :=
  (fix_iff hB hT hr _).2 ⟨i, hi, (pf_val (pt_lt hB hT hi)).symm⟩

theorem lw_len : (lw r).length = (lt r).length := by
  unfold lw
  rw [List.length_append, hT.lt_len]

@[expose] noncomputable def lP (r j : ℕ) : Fin 306936 :=
  wordElt (nthL [] (lw r) j) • CFSG.Sporadic.Fi24.root

theorem lw_mem {j : ℕ} (hj : j < (lt r).length) : nthL [] (lw r) j ∈ lw r :=
  nthL_mem [] (by rw [lw_len hB hT]; exact hj)

theorem letter_act {j : ℕ} (hj : j < (lt r).length) {i : ℕ} (hi : i < m r) :
    cls (lP r j) • pf (pt (F r) i) = pf (pt (F r) (ent (nthL 0 (lt r) j) i)) := by
  have h := cls_word hB (hT.lw_lt _ (lw_mem hB hT hj)) (pf (pt (F r) i))
  apply Fin.ext
  unfold lP
  rw [h, pf_val (pt_lt hB hT hi), (hT.letters j hj i hi).2,
    pf_val (pt_lt hB hT (hT.letters j hj i hi).1)]

theorem letter_lt {j : ℕ} (hj : j < (lt r).length) {i : ℕ} (hi : i < m r) :
    ent (nthL 0 (lt r) j) i < m r := (hT.letters j hj i hi).1

theorem hc_ne : (hc r).length ≠ 0 := fun h => hT.hc0.1 (List.length_eq_zero_iff.1 h)

theorem nthL_hc0 : nthL [] (lw r) 0 = [] := by
  have hl : 0 < (hc r).length := Nat.pos_of_ne_zero (hc_ne hB hT)
  have e1 := nthL_eq [] (lw r) 0 (by unfold lw; rw [List.length_append]; omega)
  have e2 := nthL_eq [1] (hc r) 0 hl
  rw [e1]
  unfold lw
  rw [List.getElem_append_left hl, ← e2, hT.hc0.2]

theorem lP_zero : lP r 0 = CFSG.Sporadic.Fi24.root := by
  unfold lP
  rw [nthL_hc0 hB hT, wordElt_nil, one_smul]

theorem nthL_bw {k : ℕ} (hk : k < (bp r).length) :
    nthL [] (lw r) ((hc r).length + k) = nthL [] (bw r) k := by
  have hk' : k < (bw r).length := by rw [hT.bw_len]; exact hk
  rw [nthL_eq [] (lw r) _ (by unfold lw; rw [List.length_append]; omega), nthL_eq [] (bw r) k hk']
  unfold lw
  rw [List.getElem_append_right (by omega)]
  congr 1
  omega

theorem lP_bw {k : ℕ} (hk : k < (bp r).length) :
    lP r ((hc r).length + k) = pf (pt (F r) (nthL 0 (bp r) k)) := by
  unfold lP
  rw [nthL_bw hB hT hk]
  have hw : ∀ l ∈ nthL [] (bw r) k, l < 26 :=
    hT.lw_lt _ (by unfold lw; exact List.mem_append_right _ (nthL_mem [] (by rw [hT.bw_len]; exact hk)))
  apply Fin.ext
  rw [root_val _ hB hw, (hT.bp_pts k hk).2.symm, pf_val (pt_lt hB hT (hT.bp_pts k hk).1)]

theorem lP_fix (hr : r < 3) {j : ℕ} (hj : j < (hc r).length) : xr r • lP r j = lP r j := by
  have hW : nthL [] (lw r) j = nthL [] (hc r) j := by
    rw [nthL_eq [] (lw r) j (by unfold lw; rw [List.length_append]; omega), nthL_eq [] (hc r) j hj]
    unfold lw
    rw [List.getElem_append_left hj]
  obtain ⟨i, hi, e⟩ := hT.hc_pts _ (nthL_mem [] hj)
  have hw : ∀ l ∈ nthL [] (hc r) j, l < 26 :=
    hT.lw_lt _ (by unfold lw; exact List.mem_append_left _ (nthL_mem [] hj))
  have : lP r j = pf (pt (F r) i) := by
    apply Fin.ext
    unfold lP
    rw [hW, root_val _ hB hw, ← e, pf_val (pt_lt hB hT hi)]
  rw [this]
  exact pf_fix hB hT hr hi

end Setup

theorem c0_mem_aux (L : List ℕ) (nh : ℕ) : ∀ (l : List ℕ) (k : ℕ) (e : ℕ × ℕ),
    e ∈ List.rec (motive := fun _ => ℕ → List (ℕ × ℕ)) (fun _ => List.nil)
      (fun b _ ih k => (b, nthL 0 L (Nat.add nh k)) :: ih (Nat.succ k)) l k →
      ∃ j < l.length, e = (nthL 0 l j, nthL 0 L (nh + (k + j)))
  | [], _, _, h => absurd h List.not_mem_nil
  | b :: l, k, e, h => by
    rcases List.mem_cons.1 h with h | h
    · exact ⟨0, by simp, by rw [h]; rfl⟩
    · obtain ⟨j, hj, he⟩ := c0_mem_aux L nh l (Nat.succ k) e h
      refine ⟨j + 1, by simp; omega, ?_⟩
      rw [he]
      change (nthL 0 l j, _) = (nthL 0 l j, _)
      congr 2
      omega

section Class

variable (hB : Bridge) {r : ℕ} (hT : TwinN r)
include hB hT

@[expose] def EntryOK (r : ℕ) (e : ℕ × ℕ) : Prop :=
  e.1 < m r ∧ (∀ i < m r, ent e.2 i < m r) ∧
    ∀ i < m r, cls (pf (pt (F r) e.1)) • pf (pt (F r) i) = pf (pt (F r) (ent e.2 i))

theorem third_eq {x y : ℕ × ℕ} (hx : EntryOK r x) (hy : EntryOK r y) :
    cls (pf (pt (F r) (ent x.2 y.1))) = cls (pf (pt (F r) x.1)) *
      cls (pf (pt (F r) y.1)) * cls (pf (pt (F r) x.1)) := by
  rw [← hx.2.2 y.1 hy.1, hconj, cls_inv]

theorem entry_step (x y : ℕ × ℕ) (hx : EntryOK r x) (hy : EntryOK r y) :
    EntryOK r (ent x.2 y.1, cmpT (m r) (cmpT (m r) x.2 y.2) x.2) := by
  have hthird := third_eq hB hT hx hy
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨hx2 y.1 hy1, fun i hi => ?_, fun i hi => ?_⟩
  · dsimp only
    rw [ent_cmpT hi, ent_cmpT (hx2 i hi)]
    exact hx2 _ (hy2 _ (hx2 i hi))
  · dsimp only
    rw [hthird, mul_smul, mul_smul, hx3 i hi, hy3 _ (hx2 i hi), hx3 _ (hy2 _ (hx2 i hi)),
      ent_cmpT hi, ent_cmpT (hx2 i hi)]

theorem entry_init : ∀ e ∈ c0 r, EntryOK r e := by
  intro e he
  · unfold c0 at he
    rcases List.mem_cons.1 he with he | he
    · rw [he]
      have h0 : 0 < (lt r).length := by rw [hT.lt_len]; have := hc_ne hB hT; omega
      refine ⟨hT.m_pos, fun i hi => letter_lt hB hT h0 hi, fun i hi => ?_⟩
      dsimp only
      rw [hT.F0, ← root_eq, ← lP_zero hB hT]
      exact letter_act hB hT h0 hi
    · obtain ⟨j, hj, rfl⟩ := c0_mem_aux (lt r) (lenL (hc r)) (bp r) 0 e he
      rw [Nat.zero_add, lenL_eq]
      have hjl : (hc r).length + j < (lt r).length := by
        rw [hT.lt_len, hT.bw_len]; omega
      refine ⟨(hT.bp_pts j hj).1, fun i hi => letter_lt hB hT hjl hi, fun i hi => ?_⟩
      dsimp only
      rw [← lP_bw hB hT hj]
      exact letter_act hB hT hjl hi

theorem entry_ok : ∀ e ∈ cl r, EntryOK r e :=
  cBuild_mem (EntryOK r) (entry_step hB hT) (entry_init hB hT) hT.cd_ok

theorem T0_act {i : ℕ} (hi : i < m r) :
    cls CFSG.Sporadic.Fi24.root • pf (pt (F r) i) = pf (pt (F r) (ent (nthL 0 (lt r) 0) i)) := by
  have h0 : 0 < (lt r).length := by rw [hT.lt_len]; have := hc_ne hB hT; omega
  rw [← lP_zero hB hT]
  exact letter_act hB hT h0 hi

theorem ent_eq_iff {T i : ℕ} (hi : i < m r) (hT' : ent T i < m r) {c : R}
    (hc : c • pf (pt (F r) i) = pf (pt (F r) (ent T i))) :
    c • pf (pt (F r) i) = pf (pt (F r) i) ↔ ent T i = i := by
  rw [hc]
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [pf_val (pt_lt hB hT hT'), pf_val (pt_lt hB hT hi)] at this
    exact pt_inj hB hT hT' hi this
  · intro h
    rw [h]

theorem entry_twin (hr : r < 3) {e : ℕ × ℕ} (he : e ∈ (cl r).tail) :
    TabFi23.Twin cls (xr r) CFSG.Sporadic.Fi24.root (pf (pt (F r) e.1)) := by
  have he' : e ∈ cl r := List.mem_of_mem_tail he
  obtain ⟨h1, h2, h3⟩ := entry_ok hB hT e he'
  obtain ⟨r1, r2⟩ := hT.rows e he
  have hT0 : ∀ i < m r, ent (nthL 0 (lt r) 0) i < m r := fun i hi =>
    letter_lt hB hT (by rw [hT.lt_len]; have := hc_ne hB hT; omega) hi
  have hp0 : e.1 ≠ 0 := by
    intro h
    apply r1
    rw [h]
    refine (ent_eq_iff hB hT hT.m_pos (hT0 0 hT.m_pos) (T0_act hB hT hT.m_pos)).1 ?_
    rw [hT.F0, ← root_eq]
    exact (comm_iff _ _).1 rfl
  refine ⟨?_, pf_fix hB hT hr h1, ?_, ?_, ?_⟩
  · rw [root_eq, ← hT.F0]
    exact pf_fix hB hT hr hT.m_pos
  · intro h
    have := congrArg Fin.val h
    rw [root_eq, pf_val (by norm_num), pf_val (pt_lt hB hT h1), ← hT.F0] at this
    exact hp0 (pt_inj hB hT h1 hT.m_pos this.symm)
  · intro h
    apply r1
    exact (ent_eq_iff hB hT h1 (hT0 _ h1) (T0_act hB hT h1)).1 ((comm_iff _ _).1 h)
  · intro c hc hc0 hcp
    obtain ⟨i, hi, hci⟩ := (fix_iff hB hT hr c).1 hc
    have hcpf : c = pf (pt (F r) i) := by rw [hci, pf_of]
    subst hcpf
    have hi0 : i ≠ 0 := fun h => hc0 (by rw [h, hT.F0]; rfl)
    have hip : i ≠ e.1 := fun h => hcp (by rw [h])
    rw [eq_comm, comm_iff, eq_comm (a := cls (pf (pt (F r) i)) * cls (pf (pt (F r) e.1))), comm_iff,
      ent_eq_iff hB hT hi (hT0 i hi) (T0_act hB hT hi), ent_eq_iff hB hT hi (h2 i hi) (h3 i hi)]
    exact r2 i hi hi0 hip

end Class

section Cover

variable (hB : Bridge) {r : ℕ} (hT : TwinN r)

theorem root_act (hB : Bridge) (y : Fin 306936) :
    (cls CFSG.Sporadic.Fi24.root • y).val = cP NW NT [26] y.val := by
  rw [cls_root, tR_val hB]
  change _ = CF NW NT 26 y.val
  unfold CF
  rw [if_pos rfl]

include hB hT

@[expose] noncomputable def H (r : ℕ) : Subgroup R :=
  Subgroup.closure (Set.range fun j : Fin (hc r).length => cls (lP r j))

theorem H_comm (hr : r < 3) : ∀ h ∈ H r, h * xr r = xr r * h := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    have hf := lP_fix hB hT hr j.2
    unfold xr at hf ⊢
    rw [CFSG.Sporadic.Fi24.jR_smul] at hf
    exact cls_commute_of_fix hf
  | one => rw [one_mul, mul_one]
  | mul u v _ _ hu hv => rw [mul_assoc, hv, ← mul_assoc, hu, mul_assoc]
  | inv u _ hu =>
    calc u⁻¹ * xr r = u⁻¹ * (xr r * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * xr r) * u⁻¹ := by rw [hu]
      _ = xr r * u⁻¹ := by group

theorem hc_elt {W : List ℕ} (hW : W ∈ hc r) :
    ∃ g ∈ H r, ∀ y : Fin 306936, (g • y).val = cP NW NT (dW W) y.val := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hW
  have hl : nthL [] (lw r) j = (hc r)[j] := by
    rw [nthL_eq [] (lw r) j (by unfold lw; rw [List.length_append]; omega)]
    unfold lw
    rw [List.getElem_append_left hj]
  refine ⟨cls (lP r j), Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩, fun y => ?_⟩
  have hw : ∀ l ∈ (hc r)[j], l < 26 :=
    hT.lw_lt _ (by unfold lw; exact List.mem_append_left _ (List.getElem_mem hj))
  unfold lP
  rw [hl]
  exact cls_word hB hw y

theorem inw_elt : ∀ (l : List (List ℕ)), (∀ w ∈ l, w ∈ (hc r).map dW) →
    ∃ g ∈ H r, ∀ y : Fin 306936, (g • y).val = cP NW NT l.flatten y.val
  | [], _ => ⟨1, (H r).one_mem, fun y => by rw [one_smul]; rfl⟩
  | w :: l, h => by
    obtain ⟨W, hW, rfl⟩ := List.mem_map.1 (h w List.mem_cons_self)
    obtain ⟨g, hg, eg⟩ := hc_elt hB hT hW
    obtain ⟨g', hg', eg'⟩ := inw_elt l (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
    refine ⟨g * g', (H r).mul_mem hg hg', fun y => ?_⟩
    rw [mul_smul, eg, eg', List.flatten_cons, cP_append]

theorem cover {i : ℕ} (hi : i < m r) : ∃ h ∈ H r, h • pf (pt (F r) i) = CFSG.Sporadic.Fi24.root := by
  obtain ⟨v, ⟨l, hl, rfl⟩, hv⟩ := hT.cover i hi
  obtain ⟨g, hg, eg⟩ := inw_elt hB hT l hl
  refine ⟨g, hg, Fin.ext ?_⟩
  rw [eg, pf_val (pt_lt hB hT hi), hv]

theorem cover' (hr : r < 3) {a : Fin 306936} (ha : xr r • a = a) :
    ∃ h ∈ H r, h • a = CFSG.Sporadic.Fi24.root := by
  obtain ⟨i, hi, e⟩ := (fix_iff hB hT hr a).1 ha
  have : a = pf (pt (F r) i) := by rw [e, pf_of]
  rw [this]
  exact cover hB hT hi

theorem twin_smul' (hr : r < 3) {h : R} (hh : h ∈ H r) {a b : Fin 306936}
    (hab : TabFi23.Twin cls (xr r) a b) : TabFi23.Twin cls (xr r) (h • a) (h • b) :=
  TabFi23.twin_smul hconj (H_comm hB hT hr h hh) hab

theorem twin0_in (hr : r < 3) {b : Fin 306936}
    (h : TabFi23.Twin cls (xr r) CFSG.Sporadic.Fi24.root b) :
    ∃ e ∈ cl r, b = pf (pt (F r) e.1) := by
  obtain ⟨-, hb, hab, hnc, hrow⟩ := h
  obtain ⟨i, hi, hbi⟩ := (fix_iff hB hT hr b).1 hb
  have hbpf : b = pf (pt (F r) i) := by rw [← pf_of b, ← hbi]
  have hnT : cP NW NT [26] b.val ≠ b.val := by
    intro e
    apply hnc
    refine (comm_iff _ _).2 (Fin.ext ?_)
    rw [root_act hB, e]
  have htest : ∀ W ∈ xt r, cP NW NT [26] (cP NW NT (invC W) (pt (F r) i)) =
      cP NW NT (invC W) (pt (F r) i) := by
    intro W hW
    obtain ⟨t0, tT, j, hj, hjt⟩ := hT.tests.1 W hW
    have hWl : ∀ l ∈ W, l < 26 := hT.xt_lt W hW
    set t := wordElt W • CFSG.Sporadic.Fi24.root with ht
    have htv : t.val = cP NW NT W 0 := root_val W hB hWl
    have htf : xr r • t = t := by
      have : t = pf (pt (F r) j) := Fin.ext (by rw [htv, pf_val (pt_lt hB hT hj)]; exact hjt.symm)
      rw [this]
      exact pf_fix hB hT hr hj
    have ht0 : t ≠ CFSG.Sporadic.Fi24.root := fun e => t0 (by rw [← htv, e])
    have hct : cls CFSG.Sporadic.Fi24.root • t = t := Fin.ext (by rw [root_act hB, htv]; exact tT)
    have htb : t ≠ b := by
      intro e
      apply hnT
      rw [← e, ← root_act hB, hct]
    have hrow' := hrow t htf ht0 htb
    have h1 : cls t * cls CFSG.Sporadic.Fi24.root = cls CFSG.Sporadic.Fi24.root * cls t :=
      ((comm_iff _ _).2 hct).symm
    have h2 := hrow'.1 h1
    have h3 : cls t • b = b := (comm_iff _ _).1 h2
    have h4 := (TF_iff hB hWl b).2 h3
    rw [hbi]
    exact h4.2
  obtain ⟨e, he, hpe⟩ := hT.tests.2 i hi (by rw [hbi]; exact hnT) htest
  exact ⟨e, he, by rw [hbpf, hpe]⟩

theorem cl_tail_ne : (cl r).tail ≠ [] := by
  obtain ⟨D, hD⟩ := cBuild_prefix (m r) (cd r) (c0 r)
  unfold cl
  rw [hD]
  unfold c0
  obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil hT.bp_ne
  rw [hbl]
  simp

theorem hK1 (hr : r < 3) (a : Fin 306936) (ha : xr r • a = a) :
    ∃ b, TabFi23.Twin cls (xr r) a b := by
  obtain ⟨h, hh, ha0⟩ := cover' hB hT hr ha
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (cl_tail_ne hB hT)
  have tw := entry_twin hB hT hr he
  have tw' := twin_smul' hB hT hr ((H r).inv_mem hh) tw
  rw [← ha0, inv_smul_smul] at tw'
  exact ⟨_, tw'⟩

end Cover

section Two

@[expose] def p1 : Fin 306936 := pf 305530

@[expose] noncomputable def sA : R := cls CFSG.Sporadic.Fi24.root * cls p1

theorem ev_lt' : ∀ l ∈ CFSG.KD.Fi24TwinK.ev, l < 26 := by decide

theorem cP_eq_wN : ∀ (w : List ℕ), (∀ l ∈ w, l < 26) → ∀ x, cP NW NT w x = CFSG.KS.Fi24Kit.wN NW w x
  | [], _, _ => rfl
  | l :: w, h, x => by
    rw [cP_cons, cP_eq_wN w (fun l' hl' => h l' (List.mem_cons_of_mem l hl')) x]
    unfold CF
    rw [if_neg (by have := h l List.mem_cons_self; omega)]
    rfl

theorem ev_word_fix (hB : Bridge) : ∀ (w : List ℕ), (∀ l ∈ w, l ∈ CFSG.KD.Fi24TwinK.ev) →
    cP NW NT w 0 = 0 ∧ cP NW NT w 305530 = 305530
  | [], _ => ⟨rfl, rfl⟩
  | l :: w, h => by
    obtain ⟨a, b⟩ := ev_word_fix hB w (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
    have hl := h l List.mem_cons_self
    obtain ⟨c, d⟩ := CFSG.KD.Fi24TwinK.ev_fix l hl
    rw [cP_cons, cP_cons, a, b]
    unfold CF
    simp only [show l ≠ 26 by have := ev_lt' l hl; omega, if_false]
    exact ⟨c, d⟩

theorem sA_inv : sA⁻¹ = cls p1 * cls CFSG.Sporadic.Fi24.root := by
  unfold sA
  rw [mul_inv_rev, cls_inv, cls_inv]

theorem inv_line (hB : Bridge) (d : Fin 306936) (h : cls d * sA * cls d = sA⁻¹) :
    d.val = 0 ∨ d.val = 305530 ∨ d.val = 73618 := by
  by_contra hne
  push Not at hne
  obtain ⟨h0, h1, h2⟩ := hne
  obtain ⟨w, hw, hrep⟩ := CFSG.KD.Fi24ThreeAK.cover_fact d.2 h0 h2 h1
  have hwl : ∀ l ∈ w, l < 26 := fun l hl => ev_lt' l (hw l hl)
  set g := wordElt w
  have hgv : ∀ y : Fin 306936, (g • y).val = cP NW NT w y.val := word_val hB w hwl
  obtain ⟨f0, f1⟩ := ev_word_fix hB w hw
  have hg0 : g • CFSG.Sporadic.Fi24.root = CFSG.Sporadic.Fi24.root := Fin.ext (by rw [hgv]; exact f0)
  have hg1 : g • p1 = p1 := Fin.ext (by rw [hgv]; exact f1)
  have hc : ∀ k : Fin 306936, g • k = k → jR g * cls k = cls k * jR g := fun k hk =>
    (cls_commute_of_fix hk).symm
  have hgs : jR g * sA = sA * jR g := by
    unfold sA
    rw [← mul_assoc, hc _ hg0, mul_assoc, hc _ hg1, mul_assoc]
  have hcls : cls (g • d) = jR g * cls d * (jR g)⁻¹ := CFSG.Sporadic.Fi24.cls_smul g d
  have hinv : cls (g • d) * sA * cls (g • d) = sA⁻¹ := by
    have hgs' : (jR g)⁻¹ * sA = sA * (jR g)⁻¹ := by
      calc (jR g)⁻¹ * sA = (jR g)⁻¹ * (sA * jR g) * (jR g)⁻¹ := by group
        _ = (jR g)⁻¹ * (jR g * sA) * (jR g)⁻¹ := by rw [hgs]
        _ = sA * (jR g)⁻¹ := by group
    have hgsi : jR g * sA⁻¹ = sA⁻¹ * jR g := by
      calc jR g * sA⁻¹ = sA⁻¹ * (sA * jR g) * sA⁻¹ := by group
        _ = sA⁻¹ * (jR g * sA) * sA⁻¹ := by rw [hgs]
        _ = sA⁻¹ * jR g := by group
    rw [hcls]
    calc jR g * cls d * (jR g)⁻¹ * sA * (jR g * cls d * (jR g)⁻¹)
        = jR g * cls d * ((jR g)⁻¹ * sA) * jR g * cls d * (jR g)⁻¹ := by group
      _ = jR g * cls d * (sA * (jR g)⁻¹) * jR g * cls d * (jR g)⁻¹ := by rw [hgs']
      _ = jR g * (cls d * sA * cls d) * (jR g)⁻¹ := by group
      _ = jR g * sA⁻¹ * (jR g)⁻¹ := by rw [h]
      _ = sA⁻¹ := by rw [hgsi, mul_inv_cancel_right]
  have hrv : (g • d).val = CFSG.KS.Fi24Kit.wN NW w d.val := by rw [hgv, cP_eq_wN w hwl]
  have key : ∀ i < 5, CFSG.KD.Fi24ThreeAK.nthN CFSG.KD.Fi24ThreeAK.reps i = (g • d).val → False := by
    intro i hi hie
    have hq : CFSG.KD.Fi24ThreeAK.nthN CFSG.KD.Fi24ThreeAK.tests i < 306936 := by
      interval_cases i <;> decide
    have hfail := CFSG.KD.Fi24ThreeAK.fail_fact i hi
    apply hfail
    set q : Fin 306936 := ⟨_, hq⟩
    set c := g • d
    have e := congrArg (fun z : R => (z • q).val) hinv
    change ((cls c * sA * cls c) • q).val = (sA⁻¹ • q).val at e
    rw [sA_inv, mul_smul, mul_smul, sA, mul_smul, mul_smul] at e
    rw [hB.cls, hB.cls, hB.cls, hB.cls, hB.cls, hB.cls] at e
    unfold CFSG.KC.Fi24ThreeAK.sK CFSG.KC.Fi24ThreeAK.sKi
    rw [CFSG.KS.Fi24NetPt.strictN_eq, CFSG.KS.Fi24NetPt.strictN_eq, hie]
    exact e
  have hmem : (g • d).val ∈ CFSG.KD.Fi24ThreeAK.reps := by rw [hrv]; exact hrep
  have hreps : CFSG.KD.Fi24ThreeAK.reps = [1, 2, 3, 5, 13] := rfl
  rw [hreps] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with e | e | e | e | e
  · exact key 0 (by norm_num) e.symm
  · exact key 1 (by norm_num) e.symm
  · exact key 2 (by norm_num) e.symm
  · exact key 3 (by norm_num) e.symm
  · exact key 4 (by norm_num) e.symm

variable (hB : Bridge) {r : ℕ} (hT : TwinN r)
include hB hT

theorem hK2 (hr : r < 3) (a b a' b' : Fin 306936) (hab : TabFi23.Twin cls (xr r) a b)
    (hab' : TabFi23.Twin cls (xr r) a' b') (he : cls a' * cls b' = cls a * cls b) :
    (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = cls a • b) ∨ (a' = cls a • b ∧ b' = a) := by
  obtain ⟨h, hh, ha0⟩ := cover' hB hT hr hab.1
  have tw := twin_smul' hB hT hr hh hab
  rw [ha0] at tw
  obtain ⟨e, hem, hbe⟩ := twin0_in hB hT hr tw
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hem
  have hj0 : j ≠ 0 := by
    rintro rfl
    have h0 : (cl r)[0] = nthP (cl r) 0 := (nthL_eq (0, 0) (cl r) 0 hj).symm
    rw [h0, hT.head] at hbe
    apply tw.2.2.1
    rw [hbe]
    change CFSG.Sporadic.Fi24.root = pf (pt (F r) 0)
    rw [hT.F0]
    rfl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hk : k < (gt r).length := by have := hT.conj.1; omega
  obtain ⟨g0, g1⟩ := hT.conj.2 k hk
  have hgl : ∀ l ∈ nthL [] (gt r) k, l < 26 := hT.gt_lt _ (nthL_mem [] hk)
  set g := wordElt (nthL [] (gt r) k)
  have hgv : ∀ y : Fin 306936, (g • y).val = cP NW NT (nthL [] (gt r) k) y.val := word_val hB _ hgl
  have he' : nthP (cl r) (k + 1) = (cl r)[k + 1] := nthL_eq (0, 0) (cl r) (k + 1) hj
  set u : R := jR g * h
  have hua : u • a = CFSG.Sporadic.Fi24.root := by
    change (jR g * h) • a = _
    rw [mul_smul, ha0, CFSG.Sporadic.Fi24.jR_smul]
    exact Fin.ext (by rw [hgv]; exact g0)
  have hub : u • b = p1 := by
    change (jR g * h) • b = _
    rw [mul_smul, hbe, CFSG.Sporadic.Fi24.jR_smul]
    apply Fin.ext
    rw [hgv, ← he', pf_val (pt_lt hB hT (entry_ok hB hT _ (nthP_mem hj)).1), g1]
    rfl
  have hcu : ∀ y, cls (u • y) = u * cls y * u⁻¹ := fun y => hconj u y
  have hsA : cls (u • a') * cls (u • b') = sA := by
    rw [hcu, hcu]
    calc u * cls a' * u⁻¹ * (u * cls b' * u⁻¹) = u * (cls a' * cls b') * u⁻¹ := by group
      _ = u * (cls a * cls b) * u⁻¹ := by rw [he]
      _ = u * cls a * u⁻¹ * (u * cls b * u⁻¹) := by group
      _ = sA := by rw [← hcu, ← hcu, hua, hub]; rfl
  set d := u • a'
  have hb' : cls (u • b') = cls d * sA := by
    rw [← hsA, ← mul_assoc, cls_mul_self, one_mul]
  have hinv : cls d * sA * cls d = sA⁻¹ := by
    have h2 := cls_mul_self (u • b')
    rw [hb'] at h2
    have : cls d * sA * cls d * sA = 1 := by rw [← h2]; group
    exact eq_inv_of_mul_eq_one_left this
  have hb'' : cls b' = cls a' * (cls a * cls b) := by
    rw [← he, ← mul_assoc, cls_mul_self, one_mul]
  have hnc : cls a * cls b ≠ cls b * cls a := hab.2.2.2.1
  have hthird : (u • (cls a • b)).val = 73618 := by
    rw [← mul_smul, show u * cls a = cls (u • a) * u by rw [hcu]; group, mul_smul, hua, hub,
      hB.cls]
    exact CFSG.KD.Fi24ThreeAK.line_fact
  rcases inv_line hB d hinv with h0 | h0 | h0
  · have : a' = a := smul_left_cancel u (Fin.ext (by rw [h0, hua]))
    subst this
    refine Or.inl ⟨rfl, CFSG.Sporadic.Fi24.cls_injective ?_⟩
    rw [hb'', ← mul_assoc, cls_mul_self, one_mul]
  · have : a' = b := smul_left_cancel u (Fin.ext (by rw [h0, hub]; rfl))
    refine Or.inr (Or.inl ⟨this, CFSG.Sporadic.Fi24.cls_injective ?_⟩)
    have e3 : cls a * cls b * (cls a * cls b) * (cls a * cls b) = 1 := cls_cube hnc
    rw [hb'', this, hconj, cls_inv]
    calc cls b * (cls a * cls b) = (cls a)⁻¹ * (cls a * cls b * (cls a * cls b) * (cls a * cls b)) *
          ((cls b)⁻¹ * (cls a)⁻¹) := by group
      _ = (cls a)⁻¹ * ((cls b)⁻¹ * (cls a)⁻¹) := by rw [e3, mul_one]
      _ = cls a * cls b * cls a := by rw [cls_inv, cls_inv, mul_assoc]
  · have hc : a' = cls a • b := smul_left_cancel u (Fin.ext (by rw [h0, hthird]))
    refine Or.inr (Or.inr ⟨hc, CFSG.Sporadic.Fi24.cls_injective ?_⟩)
    rw [hb'', hc, hconj, cls_inv]
    calc cls a * cls b * cls a * (cls a * cls b) = cls a * cls b * (cls a * cls a) * cls b := by
          group
      _ = cls a := by rw [cls_mul_self, mul_one, mul_assoc, cls_mul_self, mul_one]

end Two

section Three

@[expose] noncomputable def C (r : ℕ) : Subgroup R := Subgroup.centralizer {xr r}

@[expose] def FS (r : ℕ) : Type := {f : Fin 306936 // xr r • f = f}

theorem mem_C {r : ℕ} {g : R} : g ∈ C r ↔ g * xr r = xr r * g := by
  unfold C
  rw [Subgroup.mem_centralizer_singleton_iff]

theorem C_fix {r : ℕ} {g : R} (hg : g ∈ C r) {f : Fin 306936} (hf : xr r • f = f) :
    xr r • g • f = g • f := by
  rw [← mul_smul, ← (mem_C.1 hg), mul_smul, hf]

@[expose] noncomputable def ρ (r : ℕ) : C r →* Equiv.Perm (FS r) where
  toFun g :=
    { toFun := fun f => ⟨(g : R) • f.1, C_fix g.2 f.2⟩
      invFun := fun f => ⟨((g : R))⁻¹ • f.1, C_fix ((C r).inv_mem g.2) f.2⟩
      left_inv := fun f => Subtype.ext (inv_smul_smul (g : R) f.1)
      right_inv := fun f => Subtype.ext (smul_inv_smul (g : R) f.1) }
  map_one' := Equiv.ext fun f => Subtype.ext (one_smul R f.1)
  map_mul' := fun g h => Equiv.ext fun f => Subtype.ext (mul_smul (g : R) (h : R) f.1)

theorem ρ_apply {r : ℕ} (g : C r) (f : FS r) : ((ρ r g) f).1 = (g : R) • f.1 := rfl

variable (hB : Bridge) {r : ℕ} (hT : TwinN r)
include hB hT

theorem ρ_ext (hr : r < 3) {g h : C r}
    (e : ∀ i < m r, (g : R) • pf (pt (F r) i) = (h : R) • pf (pt (F r) i)) : ρ r g = ρ r h := by
  apply Equiv.ext
  intro f
  apply Subtype.ext
  rw [ρ_apply, ρ_apply]
  obtain ⟨i, hi, hfi⟩ := (fix_iff hB hT hr f.1).1 f.2
  have : f.1 = pf (pt (F r) i) := by rw [hfi, pf_of]
  rw [this]
  exact e i hi

theorem lP_fix' (hr : r < 3) {j : ℕ} (hj : j < (lt r).length) : xr r • lP r j = lP r j := by
  by_cases hj' : j < (hc r).length
  · exact lP_fix hB hT hr hj'
  · obtain ⟨k, rfl⟩ : ∃ k, j = (hc r).length + k := ⟨j - (hc r).length, by omega⟩
    have hk : k < (bp r).length := by rw [← hT.bw_len]; have := hT.lt_len; omega
    rw [lP_bw hB hT hk]
    exact pf_fix hB hT hr (hT.bp_pts k hk).1

theorem cls_C (hr : r < 3) {a : Fin 306936} (ha : xr r • a = a) : cls a ∈ C r := by
  rw [mem_C]
  unfold xr at ha ⊢
  rw [CFSG.Sporadic.Fi24.jR_smul] at ha
  exact cls_commute_of_fix ha

@[expose] noncomputable def wE (r : ℕ) (u : List ℕ) : R := (u.map fun l => cls (lP r l)).prod

theorem wE_C (hr : r < 3) : ∀ (u : List ℕ), (∀ l ∈ u, l < (lt r).length) → wE r u ∈ C r
  | [], _ => (C r).one_mem
  | l :: u, h => by
    unfold wE
    rw [List.map_cons, List.prod_cons]
    exact (C r).mul_mem (cls_C hB hT hr (lP_fix' hB hT hr (h l List.mem_cons_self)))
      (wE_C hr u fun l' hl' => h l' (List.mem_cons_of_mem l hl'))

theorem wE_act : ∀ (u : List ℕ), (∀ l ∈ u, l < (lt r).length) → ∀ {i : ℕ}, i < m r →
    wE r u • pf (pt (F r) i) = pf (pt (F r) (wF (lt r) u i)) ∧ wF (lt r) u i < m r
  | [], _, i, hi => ⟨by unfold wE; rw [List.map_nil, List.prod_nil, one_smul]; rfl, hi⟩
  | l :: u, h, i, hi => by
    obtain ⟨e, hlt⟩ := wE_act u (fun l' hl' => h l' (List.mem_cons_of_mem l hl')) hi
    have hl := h l List.mem_cons_self
    unfold wE at e ⊢
    rw [List.map_cons, List.prod_cons, mul_smul, e, letter_act hB hT hl hlt, wF_cons]
    exact ⟨rfl, letter_lt hB hT hl hlt⟩

theorem wE_inv (u : List ℕ) : (wE r u)⁻¹ = wE r u.reverse := by
  induction u with
  | nil => unfold wE; simp
  | cons l u ih =>
    unfold wE at ih ⊢
    rw [List.map_cons, List.prod_cons, mul_inv_rev, ih, List.reverse_cons, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton, cls_inv]

@[expose] noncomputable def gE (r k : ℕ) : R := wE r (nthL [] (gw r) k)

theorem gw_lt' {k : ℕ} (hk : k < (gw r).length) : ∀ l ∈ nthL [] (gw r) k, l < (lt r).length :=
  hT.gw_lt _ (nthL_mem [] hk)

theorem gE_C (hr : r < 3) {k : ℕ} (hk : k < (gw r).length) : gE r k ∈ C r :=
  wE_C hB hT hr _ (gw_lt' hB hT hk)

theorem gE_act {k : ℕ} (hk : k < (gw r).length) {i : ℕ} (hi : i < m r) :
    gE r k • pf (pt (F r) i) = pf (pt (F r) (gF (lt r) (gw r) k i)) ∧ gF (lt r) (gw r) k i < m r :=
  wE_act hB hT _ (gw_lt' hB hT hk) hi

theorem gEi_act {k : ℕ} (hk : k < (gw r).length) {i : ℕ} (hi : i < m r) :
    (gE r k)⁻¹ • pf (pt (F r) i) = pf (pt (F r) (gFI (lt r) (gw r) k i)) ∧
      gFI (lt r) (gw r) k i < m r := by
  unfold gE
  rw [wE_inv hB hT]
  exact wE_act hB hT _ (fun l hl => gw_lt' hB hT hk l (List.mem_reverse.1 hl)) hi

@[expose] noncomputable def gC (hr : r < 3) (k : Fin (gw r).length) : C r :=
  ⟨gE r k, gE_C hB hT hr k.2⟩

@[expose] noncomputable def Q (hr : r < 3) : Subgroup (Equiv.Perm (FS r)) :=
  Subgroup.closure (Set.range fun k => ρ r (gC hB hT hr k))

@[expose] noncomputable def sE (r : ℕ) (v : List ℕ) : R :=
  v.foldr (fun e z => (if e % 2 = 0 then gE r (e / 2) else (gE r (e / 2))⁻¹) * z) 1

theorem sE_mem (hr : r < 3) : ∀ (v : List ℕ), (∀ e ∈ v, e / 2 < (gw r).length) →
    ∃ hs : sE r v ∈ C r, ρ r ⟨sE r v, hs⟩ ∈ Q hB hT hr
  | [], _ => ⟨(C r).one_mem, by
      have : (⟨sE r [], (C r).one_mem⟩ : C r) = 1 := rfl
      rw [this, map_one]
      exact (Q hB hT hr).one_mem⟩
  | e :: v, h => by
    obtain ⟨hs, hq⟩ := sE_mem hr v (fun e' he' => h e' (List.mem_cons_of_mem e he'))
    have he := h e List.mem_cons_self
    have hg : gE r (e / 2) ∈ C r := gE_C hB hT hr he
    have hq1 : ρ r ⟨gE r (e / 2), hg⟩ ∈ Q hB hT hr :=
      Subgroup.subset_closure ⟨⟨e / 2, he⟩, rfl⟩
    by_cases h2 : e % 2 = 0
    · have hm : (if e % 2 = 0 then gE r (e / 2) else (gE r (e / 2))⁻¹) * sE r v ∈ C r := by
        rw [if_pos h2]; exact (C r).mul_mem hg hs
      refine ⟨hm, ?_⟩
      have : (⟨sE r (e :: v), hm⟩ : C r) = ⟨gE r (e / 2), hg⟩ * ⟨sE r v, hs⟩ := by
        apply Subtype.ext
        change (if e % 2 = 0 then gE r (e / 2) else (gE r (e / 2))⁻¹) * sE r v = _
        rw [if_pos h2]
        rfl
      rw [this, map_mul]
      exact (Q hB hT hr).mul_mem hq1 hq
    · have hm : (if e % 2 = 0 then gE r (e / 2) else (gE r (e / 2))⁻¹) * sE r v ∈ C r := by
        rw [if_neg h2]; exact (C r).mul_mem ((C r).inv_mem hg) hs
      refine ⟨hm, ?_⟩
      have : (⟨sE r (e :: v), hm⟩ : C r) = (⟨gE r (e / 2), hg⟩)⁻¹ * ⟨sE r v, hs⟩ := by
        apply Subtype.ext
        change (if e % 2 = 0 then gE r (e / 2) else (gE r (e / 2))⁻¹) * sE r v = _
        rw [if_neg h2]
        rfl
      rw [this, map_mul, map_inv]
      exact (Q hB hT hr).mul_mem ((Q hB hT hr).inv_mem hq1) hq

theorem sE_act : ∀ (v : List ℕ), (∀ e ∈ v, e / 2 < (gw r).length) → ∀ {i : ℕ}, i < m r →
    sE r v • pf (pt (F r) i) = pf (pt (F r) (sF (lt r) (gw r) v i)) ∧ sF (lt r) (gw r) v i < m r
  | [], _, i, hi => ⟨by change (1 : R) • _ = _; rw [one_smul]; rfl, hi⟩
  | e :: v, h, i, hi => by
    obtain ⟨ev, hlt⟩ := sE_act v (fun e' he' => h e' (List.mem_cons_of_mem e he')) hi
    have he := h e List.mem_cons_self
    change ((if e % 2 = 0 then gE r (e / 2) else (gE r (e / 2))⁻¹) * sE r v) • _ =
      pf (pt (F r) ((if e % 2 = 0 then gF (lt r) (gw r) (e / 2) else gFI (lt r) (gw r) (e / 2))
        (sF (lt r) (gw r) v i))) ∧
      (if e % 2 = 0 then gF (lt r) (gw r) (e / 2) else gFI (lt r) (gw r) (e / 2))
        (sF (lt r) (gw r) v i) < m r
    rw [mul_smul, ev]
    by_cases h2 : e % 2 = 0
    · rw [if_pos h2, if_pos h2]
      exact gE_act hB hT he hlt
    · rw [if_neg h2, if_neg h2]
      exact gEi_act hB hT he hlt

@[expose] noncomputable def lC (hr : r < 3) {c : ℕ} (hc : c < (lt r).length) : C r :=
  ⟨cls (lP r c), cls_C hB hT hr (lP_fix' hB hT hr hc)⟩

theorem lC_inv (hr : r < 3) {c : ℕ} (hc : c < (lt r).length) :
    (lC hB hT hr hc)⁻¹ = lC hB hT hr hc := Subtype.ext (cls_inv _)

theorem norm_gen (hr : r < 3) {c : ℕ} (hc : c < (hc r).length) (k : Fin (gw r).length) :
    ρ r (lC hB hT hr (show c < (lt r).length by rw [hT.lt_len]; omega)) * ρ r (gC hB hT hr k) *
      (ρ r (lC hB hT hr (show c < (lt r).length by rw [hT.lt_len]; omega)))⁻¹ ∈ Q hB hT hr := by
  have hcl : c < (lt r).length := by rw [hT.lt_len]; omega
  have hcn : c < (nw r).length := by rw [hT.nw_len]; exact hc
  obtain ⟨hlen, hrow⟩ := hT.norm c hcn
  obtain ⟨hv, hact⟩ := hrow k k.2
  obtain ⟨hs, hq⟩ := sE_mem hB hT hr _ hv
  rw [← map_inv, lC_inv, ← map_mul, ← map_mul]
  convert hq using 1
  apply ρ_ext hB hT hr
  intro i hi
  change (cls (lP r c) * gE r k * cls (lP r c)) • pf (pt (F r) i) = _
  rw [mul_smul, mul_smul, letter_act hB hT hcl hi, (gE_act hB hT k.2 (letter_lt hB hT hcl hi)).1,
    letter_act hB hT hcl (gE_act hB hT k.2 (letter_lt hB hT hcl hi)).2, hact i hi,
    (sE_act hB hT _ hv hi).1]

theorem norm_letter (hr : r < 3) {c : ℕ} (hc : c < (hc r).length) :
    ∀ q ∈ Q hB hT hr, ρ r (lC hB hT hr (show c < (lt r).length by rw [hT.lt_len]; omega)) * q *
      (ρ r (lC hB hT hr (show c < (lt r).length by rw [hT.lt_len]; omega)))⁻¹ ∈ Q hB hT hr := by
  intro q hq
  set g := ρ r (lC hB hT hr (show c < (lt r).length by rw [hT.lt_len]; omega))
  induction hq using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    exact norm_gen hB hT hr hc k
  | one => rw [mul_one, mul_inv_cancel]; exact (Q hB hT hr).one_mem
  | mul u v _ _ hu hv =>
    have : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
    rw [this]
    exact (Q hB hT hr).mul_mem hu hv
  | inv u _ hu =>
    have : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
    rw [this]
    exact (Q hB hT hr).inv_mem hu

theorem H_le_C (hr : r < 3) {h : R} (hh : h ∈ H r) : h ∈ C r := mem_C.2 (H_comm hB hT hr h hh)

theorem norm_H (hr : r < 3) {h : R} (hh : h ∈ H r) :
    ∀ q ∈ Q hB hT hr, ρ r ⟨h, H_le_C hB hT hr hh⟩ * q * (ρ r ⟨h, H_le_C hB hT hr hh⟩)⁻¹ ∈ Q hB hT hr ∧
      (ρ r ⟨h, H_le_C hB hT hr hh⟩)⁻¹ * q * ρ r ⟨h, H_le_C hB hT hr hh⟩ ∈ Q hB hT hr := by
  induction hh using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨⟨c, hc⟩, rfl⟩ := hz
    intro q hq
    have e : (⟨cls (lP r c), H_le_C hB hT hr (Subgroup.subset_closure ⟨⟨c, hc⟩, rfl⟩)⟩ : C r) =
        lC hB hT hr (show c < (lt r).length by rw [hT.lt_len]; omega) := rfl
    rw [e]
    refine ⟨norm_letter hB hT hr hc q hq, ?_⟩
    have := norm_letter hB hT hr hc q hq
    rw [← map_inv, lC_inv] at this
    rw [← map_inv, lC_inv]
    exact this
  | one =>
    intro q hq
    have e : (⟨1, H_le_C hB hT hr (H r).one_mem⟩ : C r) = 1 := rfl
    rw [e, map_one, inv_one, one_mul, mul_one]
    exact ⟨hq, hq⟩
  | mul u v hu' hv' hu hv =>
    intro q hq
    have e : (⟨u * v, H_le_C hB hT hr ((H r).mul_mem hu' hv')⟩ : C r) =
        ⟨u, H_le_C hB hT hr hu'⟩ * ⟨v, H_le_C hB hT hr hv'⟩ := rfl
    rw [e, map_mul]
    constructor
    · have := (hu _ (hv q hq).1).1
      rw [show ρ r ⟨u, _⟩ * ρ r ⟨v, _⟩ * q * (ρ r ⟨u, _⟩ * ρ r ⟨v, _⟩)⁻¹ =
        ρ r ⟨u, H_le_C hB hT hr hu'⟩ * (ρ r ⟨v, H_le_C hB hT hr hv'⟩ * q *
          (ρ r ⟨v, H_le_C hB hT hr hv'⟩)⁻¹) * (ρ r ⟨u, H_le_C hB hT hr hu'⟩)⁻¹ by group]
      exact this
    · have := (hv _ (hu q hq).2).2
      rw [show (ρ r ⟨u, _⟩ * ρ r ⟨v, _⟩)⁻¹ * q * (ρ r ⟨u, _⟩ * ρ r ⟨v, _⟩) =
        (ρ r ⟨v, H_le_C hB hT hr hv'⟩)⁻¹ * ((ρ r ⟨u, H_le_C hB hT hr hu'⟩)⁻¹ * q *
          ρ r ⟨u, H_le_C hB hT hr hu'⟩) * ρ r ⟨v, H_le_C hB hT hr hv'⟩ by group]
      exact this
  | inv u hu' hu =>
    intro q hq
    have e : (⟨u⁻¹, H_le_C hB hT hr ((H r).inv_mem hu')⟩ : C r) = (⟨u, H_le_C hB hT hr hu'⟩)⁻¹ := rfl
    rw [e, map_inv, inv_inv]
    exact ⟨(hu q hq).2, (hu q hq).1⟩

theorem c0_Q (hr : r < 3) : ∀ e ∈ cl r, EntryOK r e ∧
    ∀ hm : cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) e.1)) ∈ C r,
      ρ r ⟨_, hm⟩ ∈ Q hB hT hr := by
  have h0C : cls CFSG.Sporadic.Fi24.root ∈ C r := by
    rw [root_eq, ← hT.F0]
    exact cls_C hB hT hr (pf_fix hB hT hr hT.m_pos)
  refine cBuild_mem (fun e => EntryOK r e ∧ ∀ hm : cls CFSG.Sporadic.Fi24.root *
      cls (pf (pt (F r) e.1)) ∈ C r, ρ r ⟨_, hm⟩ ∈ Q hB hT hr) ?_
    (fun e he => ⟨entry_init hB hT e he, ?_⟩) hT.cd_ok
  · rintro x y ⟨hx, qx⟩ ⟨hy, qy⟩
    refine ⟨entry_step hB hT x y hx hy, fun hm => ?_⟩
    · have hxC : cls (pf (pt (F r) x.1)) ∈ C r := cls_C hB hT hr (pf_fix hB hT hr hx.1)
      have hyC : cls (pf (pt (F r) y.1)) ∈ C r := cls_C hB hT hr (pf_fix hB hT hr hy.1)
      have mx := (C r).mul_mem h0C hxC
      have my := (C r).mul_mem h0C hyC
      have qx' := qx mx
      have qy' := qy my
      have hthird := third_eq hB hT hx hy
      have e : (⟨_, hm⟩ : C r) = ⟨_, mx⟩ * (⟨_, my⟩)⁻¹ * ⟨_, mx⟩ := by
        apply Subtype.ext
        change cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) (ent x.2 y.1))) =
          cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) x.1)) *
            (cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) y.1)))⁻¹ *
            (cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) x.1)))
        rw [hthird, mul_inv_rev, cls_inv, cls_inv]
        calc cls CFSG.Sporadic.Fi24.root * (cls (pf (pt (F r) x.1)) * cls (pf (pt (F r) y.1)) *
              cls (pf (pt (F r) x.1)))
            = cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) x.1)) * cls (pf (pt (F r) y.1)) *
              (cls CFSG.Sporadic.Fi24.root * cls CFSG.Sporadic.Fi24.root) *
              cls (pf (pt (F r) x.1)) := by rw [cls_mul_self]; group
          _ = _ := by group
      rw [e, map_mul, map_mul, map_inv]
      exact (Q hB hT hr).mul_mem ((Q hB hT hr).mul_mem qx' ((Q hB hT hr).inv_mem qy')) qx'
  · intro hm
    unfold c0 at he
    rcases List.mem_cons.1 he with he | he
    · subst he
      have e : (⟨_, hm⟩ : C r) = 1 := by
        apply Subtype.ext
        change cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) 0)) = 1
        rw [hT.F0, ← root_eq, cls_mul_self]
      rw [e, map_one]
      exact (Q hB hT hr).one_mem
    · obtain ⟨j, hj, rfl⟩ := c0_mem_aux (lt r) (lenL (hc r)) (bp r) 0 _ he
      have hjg : j < (gw r).length := Nat.lt_of_lt_of_le hj hT.bp_le
      have e : (⟨_, hm⟩ : C r) = gC hB hT hr ⟨j, hjg⟩ := by
        apply Subtype.ext
        change _ = gE r j
        unfold gE wE
        rw [hT.gw_b j hj]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [lP_zero hB hT, lP_bw hB hT hj]
      rw [e]
      exact Subgroup.subset_closure ⟨⟨j, hjg⟩, rfl⟩

theorem twin_prod_C (hr : r < 3) {a b : Fin 306936} (hab : TabFi23.Twin cls (xr r) a b) :
    cls a * cls b ∈ C r :=
  (C r).mul_mem (cls_C hB hT hr hab.1) (cls_C hB hT hr hab.2.1)

theorem twin_Q (hr : r < 3) {a b : Fin 306936} (hab : TabFi23.Twin cls (xr r) a b) :
    ρ r ⟨_, twin_prod_C hB hT hr hab⟩ ∈ Q hB hT hr := by
  obtain ⟨h, hh, ha0⟩ := cover' hB hT hr hab.1
  have tw := twin_smul' hB hT hr hh hab
  rw [ha0] at tw
  obtain ⟨e, hem, hbe⟩ := twin0_in hB hT hr tw
  have hC := H_le_C hB hT hr hh
  have h0C : cls CFSG.Sporadic.Fi24.root ∈ C r := by
    rw [root_eq, ← hT.F0]
    exact cls_C hB hT hr (pf_fix hB hT hr hT.m_pos)
  have hmC : cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) e.1)) ∈ C r :=
    (C r).mul_mem h0C (cls_C hB hT hr (pf_fix hB hT hr (entry_ok hB hT e hem).1))
  have hq := (c0_Q hB hT hr e hem).2 hmC
  have eq : (⟨_, twin_prod_C hB hT hr hab⟩ : C r) =
      (⟨h, hC⟩)⁻¹ * ⟨_, hmC⟩ * ⟨h, hC⟩ := by
    apply Subtype.ext
    change cls a * cls b = h⁻¹ * (cls CFSG.Sporadic.Fi24.root * cls (pf (pt (F r) e.1))) * h
    rw [← ha0, ← hbe, hconj, hconj]
    group
  rw [eq, map_mul, map_mul, map_inv]
  exact (norm_H hB hT hr hh _ hq).2

theorem gC_act (hr : r < 3) (k : Fin (gw r).length) {i : ℕ} (hi : i < m r) :
    ((gC hB hT hr k : C r) : R) • pf (pt (F r) i) = pf (pt (F r) (gF (lt r) (gw r) k i)) :=
  (gE_act hB hT k.2 hi).1

theorem gCi_act (hr : r < 3) (k : Fin (gw r).length) {i : ℕ} (hi : i < m r) :
    (((gC hB hT hr k)⁻¹ : C r) : R) • pf (pt (F r) i) = pf (pt (F r) (gFI (lt r) (gw r) k i)) :=
  (gEi_act hB hT k.2 hi).1

theorem class2 (hr : r < 3) : ∀ x ∈ Set.range (fun k => ρ r (gC hB hT hr k)),
    ∀ y ∈ Set.range (fun k => ρ r (gC hB hT hr k)), ∀ z ∈ Set.range (fun k => ρ r (gC hB hT hr k)),
      Commute (x⁻¹ * y⁻¹ * x * y) z := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨l, rfl⟩
  have bi := fun {x : ℕ} (hx : x < m r) => (gE_act hB hT i.2 hx).2
  have bj := fun {x : ℕ} (hx : x < m r) => (gE_act hB hT j.2 hx).2
  have bl := fun {x : ℕ} (hx : x < m r) => (gE_act hB hT l.2 hx).2
  have bii := fun {x : ℕ} (hx : x < m r) => (gEi_act hB hT i.2 hx).2
  have bji := fun {x : ℕ} (hx : x < m r) => (gEi_act hB hT j.2 hx).2
  cases hab : ab r
  ·
    have key : ∀ i j : Fin (gw r).length, i.val < j.val →
        Commute ((ρ r (gC hB hT hr i))⁻¹ * (ρ r (gC hB hT hr j))⁻¹ * ρ r (gC hB hT hr i) *
          ρ r (gC hB hT hr j)) (ρ r (gC hB hT hr l)) := by
      intro i j hij
      have bi := fun {x : ℕ} (hx : x < m r) => (gE_act hB hT i.2 hx).2
      have bj := fun {x : ℕ} (hx : x < m r) => (gE_act hB hT j.2 hx).2
      have bii := fun {x : ℕ} (hx : x < m r) => (gEi_act hB hT i.2 hx).2
      have bji := fun {x : ℕ} (hx : x < m r) => (gEi_act hB hT j.2 hx).2
      unfold Commute SemiconjBy
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      apply ρ_ext hB hT hr
      intro x hx
      have e := hT.comm.2 hab i i.2 j j.2 hij l l.2 x hx
      simp only [Subgroup.coe_mul, mul_smul]
      rw [gC_act hB hT hr l hx, gC_act hB hT hr j (bl hx), gC_act hB hT hr i (bj (bl hx)),
        gCi_act hB hT hr j (bi (bj (bl hx))), gCi_act hB hT hr i (bji (bi (bj (bl hx)))),
        gC_act hB hT hr j hx, gC_act hB hT hr i (bj hx), gCi_act hB hT hr j (bi (bj hx)),
        gCi_act hB hT hr i (bji (bi (bj hx))), gC_act hB hT hr l (bii (bji (bi (bj hx)))), e]
    rcases Nat.lt_trichotomy i.val j.val with h | h | h
    · exact key i j h
    · have : i = j := Fin.ext h
      subst this
      rw [show (ρ r (gC hB hT hr i))⁻¹ * (ρ r (gC hB hT hr i))⁻¹ * ρ r (gC hB hT hr i) *
        ρ r (gC hB hT hr i) = 1 by group]
      exact Commute.one_left _
    · have := (key j i h).inv_left
      rw [show ((ρ r (gC hB hT hr j))⁻¹ * (ρ r (gC hB hT hr i))⁻¹ * ρ r (gC hB hT hr j) *
        ρ r (gC hB hT hr i))⁻¹ = (ρ r (gC hB hT hr i))⁻¹ * (ρ r (gC hB hT hr j))⁻¹ *
          ρ r (gC hB hT hr i) * ρ r (gC hB hT hr j) by group] at this
      exact this
  ·
    have hc : ρ r (gC hB hT hr i) * ρ r (gC hB hT hr j) = ρ r (gC hB hT hr j) * ρ r (gC hB hT hr i) := by
      rw [← map_mul, ← map_mul]
      apply ρ_ext hB hT hr
      intro x hx
      simp only [Subgroup.coe_mul, mul_smul]
      rw [gC_act hB hT hr j hx, gC_act hB hT hr i (bj hx), gC_act hB hT hr i hx,
        gC_act hB hT hr j (bi hx), hT.comm.1 hab i i.2 j j.2 x hx]
    rw [show (ρ r (gC hB hT hr i))⁻¹ * (ρ r (gC hB hT hr j))⁻¹ * ρ r (gC hB hT hr i) *
      ρ r (gC hB hT hr j) = (ρ r (gC hB hT hr i))⁻¹ * (ρ r (gC hB hT hr j))⁻¹ *
        (ρ r (gC hB hT hr i) * ρ r (gC hB hT hr j)) by group, hc,
      show (ρ r (gC hB hT hr i))⁻¹ * (ρ r (gC hB hT hr j))⁻¹ *
        (ρ r (gC hB hT hr j) * ρ r (gC hB hT hr i)) = 1 by group]
    exact Commute.one_left _

theorem hK3 (hr : r < 3) (a₁ b₁ a₂ b₂ a₃ b₃ : Fin 306936) (h₁ : TabFi23.Twin cls (xr r) a₁ b₁)
    (h₂ : TabFi23.Twin cls (xr r) a₂ b₂) (h₃ : TabFi23.Twin cls (xr r) a₃ b₃) (f : Fin 306936)
    (hf : xr r • f = f) : ⁅⁅cls a₁ * cls b₁, cls a₂ * cls b₂⁆, cls a₃ * cls b₃⁆ • f = f := by
  set p₁ : C r := ⟨_, twin_prod_C hB hT hr h₁⟩
  set p₂ : C r := ⟨_, twin_prod_C hB hT hr h₂⟩
  set p₃ : C r := ⟨_, twin_prod_C hB hT hr h₃⟩
  have key := triple_comm_closure _ (class2 hB hT hr) _ (twin_Q hB hT hr h₁) _ (twin_Q hB hT hr h₂) _
    (twin_Q hB hT hr h₃)
  rw [← map_commutatorElement, ← map_commutatorElement] at key
  have e := congrArg (fun σ : Equiv.Perm (FS r) => (σ ⟨f, hf⟩).1) key
  simp only [ρ_apply, Equiv.Perm.coe_one, id_eq] at e
  have e2 : ((⁅⁅p₁, p₂⁆, p₃⁆ : C r) : R) = ⁅⁅cls a₁ * cls b₁, cls a₂ * cls b₂⁆, cls a₃ * cls b₃⁆ := by
    rw [← (C r).coe_subtype, map_commutatorElement, map_commutatorElement]
    rfl
  rw [← e2]
  exact e

end Three

theorem twinFacts_of
    (hB : Bridge) {r : ℕ} (hr : r < 3) :
    TabFi24.TwinFacts (wr r) := by
  have hT := CFSG.KD.Fi24TwinK.twin_facts r hr
  exact ⟨hK1 hB hT hr, fun a b a' b' h h' e => hK2 hB hT hr a b a' b' h h' e,
    fun a₁ b₁ a₂ b₂ a₃ b₃ h₁ h₂ h₃ f hf => hK3 hB hT hr a₁ b₁ a₂ b₂ a₃ b₃ h₁ h₂ h₃ f hf⟩

end CFSG.KD.Fi24TwinK.Group

end
