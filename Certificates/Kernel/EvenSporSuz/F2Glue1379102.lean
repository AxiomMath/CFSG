module

public import Certificates.Certificate25002
public import Certificates.Kernel.EvenSporSuz.F21379102
public import Certificates.Kernel.EvenSporSuz.SylowGlue25002
public import Certificates.Kernel.EvenSporSuz.CoverGlue
public import Certificates.Kernel.EvenSporSuz.Outer25040F
public import CFSG.Certificates.Kernel.EvenSporSuz.F2Sound

public section

namespace CertificateChecks.KernelF21379102

open CFSG.KC.ONanSmall CFSG.KC.EvenSporSuz CFSG.KC.EvenSporSuz.Syl CFSG.KC.EvenSporSuz.F2
  CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec CertificateChecks.KernelSuz CertificateChecks.KernelSyl25002
  CFSG.EvenSporadicStandard.TwoSuz
open scoped commutatorElement

noncomputable def Hm (H : Subgroup GL12) : Submonoid Mat12 := H.toSubmonoid.map (Units.coeHom Mat12)

theorem mem_Hm {H : Subgroup GL12} {x : Mat12} : x ∈ Hm H ↔ ∃ u ∈ H, vm u = x :=
  Submonoid.mem_map

def LIn (H : Subgroup GL12) (x : ℕ) : Prop := Canon3 x ∧ ∃ u ∈ H, vm u = pkMat3 x

def LetIn (H : Subgroup GL12) (M I : List ℕ) : Prop :=
  (∀ k < M.length, LIn H (M.getD k 0)) ∧ ∀ k < I.length, LIn H (I.getD k 0)

theorem evalL_in {H : Subgroup GL12} {M I : List ℕ} (h : LetIn H M I) (w : List ℕ) :
    LIn H (evalL M I w) := by
  have hM : ∀ k < M.length, Canon3 (M.getD k 0) ∧ pkMat3 (M.getD k 0) ∈ Hm H :=
    fun k hk => ⟨(h.1 k hk).1, mem_Hm.2 (h.1 k hk).2⟩
  have hI : ∀ k < I.length, Canon3 (I.getD k 0) ∧ pkMat3 (I.getD k 0) ∈ Hm H :=
    fun k hk => ⟨(h.2 k hk).1, mem_Hm.2 (h.2 k hk).2⟩
  obtain ⟨hc, hm⟩ := evalL_mem hM hI w
  exact ⟨hc, mem_Hm.1 hm⟩

theorem unit_of {a b : ℕ} (h : pkMat3 a * pkMat3 b = 1) :
    ∃ u : GL12, vm u = pkMat3 a ∧ vm u⁻¹ = pkMat3 b :=
  ⟨⟨pkMat3 a, pkMat3 b, h, mul_eq_one_comm.1 h⟩, rfl, rfl⟩

theorem vm_inv_eq {u : GL12} {a b : ℕ} (hu : vm u = pkMat3 a) (h : pkMat3 a * pkMat3 b = 1) :
    vm u⁻¹ = pkMat3 b := by
  have hu' : vm u * vm u⁻¹ = 1 := Units.mul_inv u
  calc vm u⁻¹ = pkMat3 b * pkMat3 a * vm u⁻¹ := by
        rw [mul_eq_one_comm.1 h, Matrix.one_mul]
    _ = pkMat3 b := by rw [Matrix.mul_assoc, ← hu, hu', Matrix.mul_one]

noncomputable abbrev lsub (M : List ℕ) (n : ℕ) : Subgroup GL12 :=
  Subgroup.closure {u | ∃ k < n, vm u = pkMat3 (M.getD k 0)}

theorem gen_facts {M I : List ℕ} {n : ℕ} (h : invK M I n = true) {k : ℕ} (hk : k < n) {u : GL12}
    (hu : vm u = pkMat3 (M.getD k 0)) :
    Canon3 (M.getD k 0) ∧ Canon3 (I.getD k 0) ∧ vm u⁻¹ = pkMat3 (I.getD k 0) := by
  obtain ⟨-, -, h'⟩ := invK_sound h
  obtain ⟨h1, h2, h3⟩ := h' k hk
  exact ⟨h1, h2, vm_inv_eq hu h3⟩

theorem letIn_of {H : Subgroup GL12} {M I : List ℕ} {n : ℕ} (h : invK M I n = true)
    (hH : ∀ k < n, ∀ u : GL12, vm u = pkMat3 (M.getD k 0) → u ∈ H) : LetIn H M I := by
  obtain ⟨hl, hil, hk⟩ := invK_sound h
  constructor
  · intro k hk'
    rw [hl] at hk'
    obtain ⟨hc, -, hm⟩ := hk k hk'
    obtain ⟨u, hu, -⟩ := unit_of hm
    exact ⟨hc, u, hH k hk' u hu, hu⟩
  · intro k hk'
    rw [hil] at hk'
    obtain ⟨-, hc, hm⟩ := hk k hk'
    obtain ⟨u, hu, hui⟩ := unit_of hm
    exact ⟨hc, u⁻¹, inv_mem (hH k hk' u hu), hui⟩

theorem letIn_lsub {M I : List ℕ} {n : ℕ} (h : invK M I n = true) : LetIn (lsub M n) M I :=
  letIn_of h fun k hk _ hu => Subgroup.subset_closure ⟨k, hk, hu⟩

theorem pk3 {a b c : ℕ} (ha : Canon3 a) (hb : Canon3 b) (hc : Canon3 c) :
    pkMat3 (mulF3 (mulF3 a b) c) = pkMat3 a * pkMat3 b * pkMat3 c := by
  rw [(canon3_mulF3 (canon3_mulF3 ha hb).1 hc).2, (canon3_mulF3 ha hb).2]

theorem pk4 {a b c d : ℕ} (ha : Canon3 a) (hb : Canon3 b) (hc : Canon3 c) (hd : Canon3 d) :
    pkMat3 (mulF3 (mulF3 (mulF3 a b) c) d) = pkMat3 a * pkMat3 b * pkMat3 c * pkMat3 d := by
  rw [(canon3_mulF3 (canon3_mulF3 (canon3_mulF3 ha hb).1 hc).1 hd).2, pk3 ha hb hc]

theorem conj_lane {s y w : GL12} {a b c : ℕ} (ha : Canon3 a) (hb : Canon3 b) (hc : Canon3 c)
    (hs : vm s = pkMat3 a) (hy : vm y = pkMat3 b) (hsi : vm s⁻¹ = pkMat3 c)
    (hw : vm w = pkMat3 (mulF3 (mulF3 a b) c)) : s * y * s⁻¹ = w :=
  vm_inj (by rw [hw, pk3 ha hb hc, vm_mul, vm_mul, hs, hy, hsi])

theorem comm_lane {x y w : GL12} {a b c d : ℕ} (ha : Canon3 a) (hb : Canon3 b) (hc : Canon3 c)
    (hd : Canon3 d) (hx : vm x = pkMat3 a) (hy : vm y = pkMat3 b) (hxi : vm x⁻¹ = pkMat3 c)
    (hyi : vm y⁻¹ = pkMat3 d) (hw : vm w = pkMat3 (mulF3 (mulF3 (mulF3 a b) c) d)) :
    ⁅x, y⁆ = w :=
  vm_inj (by rw [hw, pk4 ha hb hc hd, commutatorElement_def, vm_mul, vm_mul, vm_mul, hx, hy, hxi,
    hyi])

theorem eq_commutator {N U V : ℕ} (hN : Canon3 N) (hU : Canon3 U) (hV : Canon3 V)
    (h : mulF3 (mulF3 N V) U = mulF3 U V) {a b : GL12} (ha : vm a = pkMat3 U)
    (hb : vm b = pkMat3 V) : pkMat3 N = vm ⁅a, b⁆ := by
  have h1 := congrArg pkMat3 h
  rw [pk3 hN hV hU, (canon3_mulF3 hU hV).2, ← ha, ← hb] at h1
  have e : ⁅a, b⁆ * (b * a) = a * b := by
    rw [commutatorElement_def]
    group
  have h2 : vm ⁅a, b⁆ * (vm b * vm a) = vm a * vm b := by rw [← vm_mul, ← vm_mul, e, vm_mul]
  have hinv : vm b * vm a * vm (b * a)⁻¹ = 1 := by
    rw [← vm_mul, ← vm_mul, mul_inv_cancel, vm_one]
  calc pkMat3 N = pkMat3 N * (vm b * vm a) * vm (b * a)⁻¹ := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = vm ⁅a, b⁆ * (vm b * vm a) * vm (b * a)⁻¹ := by
        rw [← Matrix.mul_assoc (pkMat3 N), h1, ← h2]
    _ = vm ⁅a, b⁆ := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]

theorem mem_normalizer_of_conj {G : Type} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact h x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← hH] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  have : x = y := by
    have h' := congrArg (fun z => g⁻¹ * z * g) hyx
    simpa [mul_assoc] using h'.symm
  rw [this]
  exact hy

theorem normalizer_closure {T : Set GL12} {s : GL12}
    (h : ∀ y ∈ T, s * y * s⁻¹ ∈ Subgroup.closure T) :
    s ∈ Subgroup.normalizer (Subgroup.closure T : Set GL12) := by
  refine mem_normalizer_of_conj fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => simp
  | mul y z _ _ hy hz =>
    have e : s * (y * z) * s⁻¹ = s * y * s⁻¹ * (s * z * s⁻¹) := by group
    rw [e]
    exact mul_mem hy hz
  | inv y _ hy =>
    have e : s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hy

theorem allBelow_of {p : ℕ → Bool} : ∀ {n : ℕ}, (∀ k < n, p k = true) → allBelow n p = true
  | 0, _ => rfl
  | n + 1, h => by
    have h' : (p n && allBelow n p) = true := by
      rw [Bool.and_eq_true]
      exact ⟨h n (by omega), allBelow_of fun k hk => h k (by omega)⟩
    exact h'

theorem cen_iff {G GI : List ℕ} {n : ℕ} (hG : invK G GI n = true) {e : ℕ} (he : Canon3 e)
    {w : GL12} (hw : pkMat3 e = vm w) :
    w ∈ Subgroup.centralizer (lsub G n : Set GL12) ↔ cenB G n e = true := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  obtain ⟨-, -, hk⟩ := invK_sound hG
  constructor
  · intro h
    refine allBelow_of fun k hk' => ?_
    obtain ⟨g, hg, -⟩ := unit_of (hk k hk').2.2
    have hc := h g ⟨k, hk', hg⟩
    have hm : mulF3 e (G.getD k 0) = mulF3 (G.getD k 0) e := by
      refine canon3_inj (canon3_mulF3 he (hk k hk').1).1 (canon3_mulF3 (hk k hk').1 he).1 ?_
      rw [(canon3_mulF3 he (hk k hk').1).2, (canon3_mulF3 (hk k hk').1 he).2, hw, ← hg, ← vm_mul,
        ← vm_mul, hc]
    rw [hm]
    exact Nat.beq_refl _
  · rintro h g ⟨k, hk', hg⟩
    have hm := cenB_sound h k hk'
    refine vm_inj ?_
    rw [vm_mul, vm_mul, hg, ← hw, ← (canon3_mulF3 (hk k hk').1 he).2, ← hm,
      (canon3_mulF3 he (hk k hk').1).2]

theorem enum_facts {E : List (ℕ × ℕ)} {G GI : List ℕ} {n m : ℕ}
    (h : enumK (treeOf E) G GI n m E = true) (hi : invK G GI n = true) :
    E.length = m ∧ (E.map Prod.fst).Nodup ∧ (∀ p ∈ E, Canon3 p.1) ∧
      (∀ p ∈ E, ∃ u ∈ lsub G n, vm u = pkMat3 p.1) ∧
      ∀ u ∈ lsub G n, ∃ p ∈ E, pkMat3 p.1 = vm u := by
  obtain ⟨-, -, hk⟩ := invK_sound hi
  have hG : ∀ k < n, Canon3 (GI.getD k 0) ∧ pkMat3 (GI.getD k 0) * pkMat3 (G.getD k 0) = 1 :=
    fun k hk' => ⟨(hk k hk').2.1, mul_eq_one_comm.1 (hk k hk').2.2⟩
  obtain ⟨hl, hnd, ⟨p1, hp1, hp1e⟩, hcan, hmem, hcl⟩ := enumK_sound h hG
  refine ⟨hl, hnd, hcan,
    fun p hp => mem_Hm.1 (hmem (Hm (lsub G n)) (fun k hk' => mem_Hm.2 ?_) p hp), ?_⟩
  · obtain ⟨u, hu, -⟩ := unit_of (hk k hk').2.2
    exact ⟨u, Subgroup.subset_closure ⟨k, hk', hu⟩, hu⟩
  let Mon : Submonoid Mat12 := Submonoid.closure {x | ∃ k < n, x = pkMat3 (G.getD k 0)}
  have rmul : ∀ x ∈ Mon, ∀ p ∈ E, ∃ q ∈ E, pkMat3 q.1 = pkMat3 p.1 * x := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk', rfl⟩ := hx
      intro p hp
      obtain ⟨q, hq, hqe⟩ := hcl p hp k hk'
      exact ⟨q, hq, by rw [hqe, (canon3_mulF3 (hcan p hp) (hk k hk').1).2]⟩
    | one => exact fun p hp => ⟨p, hp, (Matrix.mul_one _).symm⟩
    | mul x y _ _ hx hy =>
      intro p hp
      obtain ⟨q, hq, hqe⟩ := hx p hp
      obtain ⟨r, hr, hre⟩ := hy q hq
      exact ⟨r, hr, by rw [hre, hqe, Matrix.mul_assoc]⟩
  have inMon : ∀ p ∈ E, pkMat3 p.1 ∈ Mon :=
    hmem Mon fun k hk' => Submonoid.subset_closure ⟨k, hk', rfl⟩
  have one' : ∃ p ∈ E, pkMat3 p.1 = vm (1 : GL12) :=
    ⟨p1, hp1, by rw [hp1e, canon3_one3.2, vm_one]⟩
  have step : ∀ x y : GL12, (∃ p ∈ E, pkMat3 p.1 = vm x) → (∃ p ∈ E, pkMat3 p.1 = vm y) →
      ∃ p ∈ E, pkMat3 p.1 = vm (x * y) := by
    rintro x y ⟨p, hp, hpx⟩ ⟨q, hq, hqy⟩
    obtain ⟨r, hr, hre⟩ := rmul _ (inMon q hq) p hp
    exact ⟨r, hr, by rw [hre, hpx, hqy, vm_mul]⟩
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk', hxk⟩ := hx
    obtain ⟨q, hq, hqe⟩ := rmul _ (Submonoid.subset_closure ⟨k, hk', rfl⟩) p1 hp1
    exact ⟨q, hq, by rw [hqe, hp1e, canon3_one3.2, Matrix.one_mul, hxk]⟩
  | one => exact one'
  | mul x y _ _ hx hy => exact step x y hx hy
  | inv x _ hx =>
    have hpow : ∀ k : ℕ, ∃ p ∈ E, pkMat3 p.1 = vm (x ^ k) := by
      intro k
      induction k with
      | zero => simpa using one'
      | succ k ih =>
        rw [pow_succ]
        exact step _ _ ih hx
    have hpos := orderOf_pos x
    have e : x ^ (orderOf x - 1) = x⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one])
    rw [← e]
    exact hpow _

theorem ncard_eq {E : List (ℕ × ℕ)} {H : Subgroup GL12} (hc : ∀ p ∈ E, Canon3 p.1)
    (hnd : (E.map Prod.fst).Nodup) (hb : ∀ p ∈ E, ∃ u ∈ H, vm u = pkMat3 p.1)
    (hf : ∀ u ∈ H, ∃ p ∈ E, pkMat3 p.1 = vm u) (Q : GL12 → Prop) (P : ℕ × ℕ → Bool)
    (hQP : ∀ p ∈ E, ∀ w : GL12, pkMat3 p.1 = vm w → (Q w ↔ P p = true)) :
    Set.ncard {w | w ∈ H ∧ Q w} = E.countP P := by
  have inj : ∀ {p q : ℕ × ℕ}, p ∈ E → q ∈ E → pkMat3 p.1 = pkMat3 q.1 → p = q :=
    fun hp hq h => List.inj_on_of_nodup_map hnd hp hq (canon3_inj (hc _ hp) (hc _ hq) h)
  rw [← Set.ncard_image_of_injective _ (fun a b (h : vm a = vm b) => vm_inj h)]
  have himg : vm '' {w | w ∈ H ∧ Q w} =
      (fun p : ℕ × ℕ => pkMat3 p.1) '' ((E.filter P).toFinset : Set (ℕ × ℕ)) := by
    ext M
    simp only [Set.mem_image, Set.mem_setOf_eq, List.coe_toFinset, List.mem_filter]
    constructor
    · rintro ⟨w, ⟨hw, hq⟩, rfl⟩
      obtain ⟨p, hp, hpw⟩ := hf w hw
      exact ⟨p, ⟨hp, (hQP p hp w hpw).1 hq⟩, hpw⟩
    · rintro ⟨p, ⟨hp, hP⟩, rfl⟩
      obtain ⟨u, hu, hue⟩ := hb p hp
      exact ⟨u, ⟨hu, (hQP p hp u hue.symm).2 hP⟩, hue⟩
  rw [himg, Set.InjOn.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup ((hnd.of_map _).filter _), List.countP_eq_length_filter]
  intro p hp q hq h
  simp only [List.coe_toFinset, List.mem_filter, Set.mem_setOf_eq] at hp hq
  exact inj hp.1 hq.1 h

theorem card_eq {E : List (ℕ × ℕ)} {H : Subgroup GL12} (hc : ∀ p ∈ E, Canon3 p.1)
    (hnd : (E.map Prod.fst).Nodup) (hb : ∀ p ∈ E, ∃ u ∈ H, vm u = pkMat3 p.1)
    (hf : ∀ u ∈ H, ∃ p ∈ E, pkMat3 p.1 = vm u) : Nat.card H = E.length := by
  have h := ncard_eq hc hnd hb hf (fun _ => True) (fun _ => true) (fun _ _ _ _ => by simp)
  rw [List.countP_true] at h
  have e : {w | w ∈ H ∧ True} = (H : Set GL12) := by
    ext w
    simp
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← e]
  exact h

theorem invs : invK gs gi 4 = true ∧ invK ab abi 5 = true ∧ invK n2 n2i 7 = true ∧
    invK n3 n3i 6 = true ∧ invK qL qL 3 = true ∧ invK ys yis 6 = true := by
  have h := inv_true
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem S_eq : Certificates.Cert25002.S = lsub gs 4 := by
  refine congrArg Subgroup.closure (Set.ext fun u => ⟨?_, ?_⟩)
  · rintro ⟨k, hk, hu⟩
    exact ⟨k, hk, by rw [hu, pkMat3_gs hk]⟩
  · rintro ⟨k, hk, hu⟩
    exact ⟨k, hk, by rw [hu, pkMat3_gs hk]⟩

theorem letS : LetIn (lsub gs 4) gs gi := letIn_lsub invs.1

theorem letN2 : LetIn (lsub n2 7) n2 n2i := letIn_lsub invs.2.2.1

theorem letN3 : LetIn (lsub n3 6) n3 n3i := letIn_lsub invs.2.2.2.1

theorem le_self_comm (H : Subgroup GL12) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem n2_le : lsub n2 7 ≤ ⁅lsub gs 4, lsub gs 4⁆ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨j, hj, hu⟩
  obtain ⟨-, hN⟩ := comK_sound n2_true
  obtain ⟨hc, he⟩ := hN j hj
  obtain ⟨hU, a, ha, hav⟩ := evalL_in letS (g2u.getD j [])
  obtain ⟨hV, b, hb, hbv⟩ := evalL_in letS (g2v.getD j [])
  rw [vm_inj (hu.trans (eq_commutator hc hU hV he hav hbv))]
  exact Subgroup.commutator_mem_commutator ha hb

theorem s_norm_n2 {s : GL12} {i : ℕ} (hi : i < 4) (hs : vm s = pkMat3 (gs.getD i 0)) :
    s ∈ Subgroup.normalizer (lsub n2 7 : Set GL12) := by
  refine normalizer_closure ?_
  rintro y ⟨j, hj, hy⟩
  have hm := memK_sound m2c_true (7 * i + j) (by omega)
  rw [show (7 * i + j) / 7 = i by omega, show (7 * i + j) % 7 = j by omega] at hm
  obtain ⟨-, w, hw, hwv⟩ := evalL_in letN2 (m2c.getD (7 * i + j) [])
  rw [hm] at hwv
  obtain ⟨ha, hai, hsi⟩ := gen_facts invs.1 hi hs
  obtain ⟨hb, -, -⟩ := gen_facts invs.2.2.1 hj hy
  rw [conj_lane ha hb hai hs hy hsi hwv]
  exact hw

theorem comm_le_n2 : ⁅lsub gs 4, lsub gs 4⁆ ≤ lsub n2 7 := by
  have hX : lsub gs 4 ≤ Subgroup.normalizer (lsub n2 7 : Set GL12) :=
    (Subgroup.closure_le _).2 fun s ⟨i, hi, hs⟩ => s_norm_n2 hi hs
  refine TauCeti.commutator_closure_closure_le
    (X := {u | ∃ k < 4, vm u = pkMat3 (gs.getD k 0)})
    (Y := {u | ∃ k < 4, vm u = pkMat3 (gs.getD k 0)}) (N := lsub n2 7) hX hX ?_
  rintro x ⟨i, hi, hx⟩ y ⟨j, hj, hy⟩
  have hm := memK_sound m2a_true (4 * i + j) (by omega)
  rw [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega] at hm
  obtain ⟨-, w, hw, hwv⟩ := evalL_in letN2 (m2a.getD (4 * i + j) [])
  rw [hm] at hwv
  obtain ⟨ha, hai, hxi⟩ := gen_facts invs.1 hi hx
  obtain ⟨hb, hbi, hyi⟩ := gen_facts invs.1 hj hy
  rw [comm_lane ha hb hai hbi hx hy hxi hyi hwv]
  exact hw

theorem n2_eq : lsub n2 7 = ⁅lsub gs 4, lsub gs 4⁆ := le_antisymm n2_le comm_le_n2

theorem n3_le : lsub n3 6 ≤ ⁅lsub n2 7, lsub gs 4⁆ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨j, hj, hu⟩
  obtain ⟨-, hN⟩ := comK_sound n3_true
  obtain ⟨hc, he⟩ := hN j hj
  obtain ⟨hU, a, ha, hav⟩ := evalL_in letN2 (m2u.getD j [])
  obtain ⟨hV, b, hb, hbv⟩ := evalL_in letS (g3v.getD j [])
  rw [vm_inj (hu.trans (eq_commutator hc hU hV he hav hbv))]
  exact Subgroup.commutator_mem_commutator ha hb

theorem s_norm_n3 {s : GL12} {i : ℕ} (hi : i < 4) (hs : vm s = pkMat3 (gs.getD i 0)) :
    s ∈ Subgroup.normalizer (lsub n3 6 : Set GL12) := by
  refine normalizer_closure ?_
  rintro y ⟨k, hk, hy⟩
  have hm := memK_sound m3c_true (6 * i + k) (by omega)
  rw [show (6 * i + k) / 6 = i by omega, show (6 * i + k) % 6 = k by omega] at hm
  obtain ⟨-, w, hw, hwv⟩ := evalL_in letN3 (m3c.getD (6 * i + k) [])
  rw [hm] at hwv
  obtain ⟨ha, hai, hsi⟩ := gen_facts invs.1 hi hs
  obtain ⟨hb, -, -⟩ := gen_facts invs.2.2.2.1 hk hy
  rw [conj_lane ha hb hai hs hy hsi hwv]
  exact hw

theorem comm_le_n3 : ⁅lsub n2 7, lsub gs 4⁆ ≤ lsub n3 6 := by
  have hY : lsub gs 4 ≤ Subgroup.normalizer (lsub n3 6 : Set GL12) :=
    (Subgroup.closure_le _).2 fun s ⟨i, hi, hs⟩ => s_norm_n3 hi hs
  have hX : lsub n2 7 ≤ Subgroup.normalizer (lsub n3 6 : Set GL12) := by
    rw [n2_eq]
    exact (le_self_comm _).trans hY
  refine TauCeti.commutator_closure_closure_le
    (X := {u | ∃ k < 7, vm u = pkMat3 (n2.getD k 0)})
    (Y := {u | ∃ k < 4, vm u = pkMat3 (gs.getD k 0)}) (N := lsub n3 6) hX hY ?_
  rintro x ⟨j, hj, hx⟩ y ⟨i, hi, hy⟩
  have hm := memK_sound m3a_true (4 * j + i) (by omega)
  rw [show (4 * j + i) / 4 = j by omega, show (4 * j + i) % 4 = i by omega] at hm
  obtain ⟨-, w, hw, hwv⟩ := evalL_in letN3 (m3a.getD (4 * j + i) [])
  rw [hm] at hwv
  obtain ⟨ha, hai, hxi⟩ := gen_facts invs.2.2.1 hj hx
  obtain ⟨hb, hbi, hyi⟩ := gen_facts invs.1 hi hy
  rw [comm_lane ha hb hai hbi hx hy hxi hyi hwv]
  exact hw

theorem gamma3 : ⁅⁅lsub gs 4, lsub gs 4⁆, lsub gs 4⁆ = lsub n3 6 := by
  rw [← n2_eq]
  exact (le_antisymm n3_le comm_le_n3).symm

theorem card_n3 : Nat.card (lsub n3 6) = 2 ^ 7 := by
  obtain ⟨hl, hnd, hc, hb, hf⟩ := enum_facts (E := els) enum3_true invs.2.2.2.1
  rw [card_eq hc hnd hb hf, hl]
  norm_num

theorem card_z :
    Nat.card (lsub n3 6 ⊓ Subgroup.centralizer (lsub n3 6 : Set GL12) : Subgroup GL12) = 32 := by
  obtain ⟨-, hnd, hc, hb, hf⟩ := enum_facts (E := els) enum3_true invs.2.2.2.1
  obtain ⟨hcnt, -⟩ := cenK_sound cen3_true
  have h := ncard_eq hc hnd hb hf (fun w => w ∈ Subgroup.centralizer (lsub n3 6 : Set GL12))
    (fun p => cenB n3 6 p.1) fun p hp _ hw => cen_iff invs.2.2.2.1 (hc p hp) hw
  rw [hcnt] at h
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact h

theorem sq_z : ∀ x ∈ lsub n3 6 ⊓ Subgroup.centralizer (lsub n3 6 : Set GL12), x * x = 1 := by
  intro x hx
  obtain ⟨-, -, hc, -, hf⟩ := enum_facts (E := els) enum3_true invs.2.2.2.1
  obtain ⟨-, hsq⟩ := cenK_sound cen3_true
  obtain ⟨p, hp, hpx⟩ := hf x hx.1
  have hcen := (cen_iff invs.2.2.2.1 (hc p hp) hpx).1 hx.2
  refine vm_inj ?_
  rw [vm_mul, ← hpx, ← (canon3_mulF3 (hc p hp) (hc p hp)).2, hsq p hp hcen, canon3_one3.2, vm_one]

theorem q_le : lsub qL 3 ≤ lsub gs 4 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨t, ht, hu⟩
  obtain ⟨-, w, hw, hwv⟩ := evalL_in letS (q.getD t [])
  rw [memK_sound q_true t ht] at hwv
  rw [vm_inj (hu.trans hwv.symm)]
  exact hw

theorem q_all : ∀ x ∈ lsub qL 3, x ∈ Subgroup.centralizer (lsub qL 3 : Set GL12) ∧ x * x = 1 := by
  intro x hx
  obtain ⟨hl, -, hc, -, hf⟩ := enum_facts (E := qels) enumQ_true invs.2.2.2.2.1
  obtain ⟨hcnt, hsq⟩ := cenK_sound cenQ_true
  rw [← hl] at hcnt
  have hall := List.countP_eq_length.1 hcnt
  obtain ⟨p, hp, hpx⟩ := hf x hx
  have hcen := hall p hp
  refine ⟨(cen_iff invs.2.2.2.2.1 (hc p hp) hpx).2 hcen, vm_inj ?_⟩
  rw [vm_mul, ← hpx, ← (canon3_mulF3 (hc p hp) (hc p hp)).2, hsq p hp hcen, canon3_one3.2, vm_one]

theorem q_comm : ∀ x ∈ lsub qL 3, ∀ y ∈ lsub qL 3, x * y = y * x := fun x hx y hy =>
  (Subgroup.mem_centralizer_iff.1 (q_all x hx).1 y hy).symm

theorem q_card : Nat.card (lsub qL 3) = 8 := by
  obtain ⟨hl, hnd, hc, hb, hf⟩ := enum_facts (E := qels) enumQ_true invs.2.2.2.2.1
  rw [card_eq hc hnd hb hf, hl]

theorem ab_mem {k : ℕ} (hk : k < 5) {u : GL12} (hu : vm u = pkMat3 (ab.getD k 0)) :
    u ∈ Certificates.Cert25002.AB := by
  have h1 : ab.getD k 0 = abL.getD k 0 := by
    have := allBelow_eq ab_true k hk
    simpa only [Nat.beq_eq] using this
  have hlen : k < abL.length := by
    simp only [abL, List.length_cons, List.length_nil]
    omega
  have h2 : abL.getD k 0 = lanesMt (abGS.mats.getD k oneM) := by
    rw [getD_indep hlen 0 one3, abL_eq, lanes_getD]
  have hv : vm (abGS.letterU abv (2 * k)) = ofMt (abGS.mats.getD k oneM) := by
    have e : 2 * k / 2 = k := by omega
    have h := GenSys.val_letterU abGS abv (2 * k)
    rw [GenSys.letter, if_pos (by omega), e] at h
    exact h
  have heq : u = abGS.letterU abv (2 * k) :=
    vm_inj (by rw [hu, h1, h2, pkMat3_lanesMt (abCanon.1 k), hv])
  rw [heq]
  exact abGS_letterU_even_mem' (fun _ h => Subgroup.subset_closure (Or.inl h))
    (fun _ h => Subgroup.subset_closure (Or.inr h)) k

theorem letAB : LetIn Certificates.Cert25002.AB ab abi :=
  letIn_of invs.2.1 fun _ hk _ hu => ab_mem hk hu

theorem c_facts : LIn Certificates.Cert25002.AB (ys.getD 4 0) ∧
    LIn Certificates.Cert25002.AB (ys.getD 5 0) ∧ cenB qL 3 (ys.getD 4 0) = true ∧
    cenB qL 3 (ys.getD 5 0) = true := by
  have h := c_true
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hm, h4⟩, h5⟩ := h
  have e4 := evalL_in letAB ([c1, c2].getD 0 [])
  have e5 := evalL_in letAB ([c1, c2].getD 1 [])
  rw [memK_sound hm 0 (by norm_num)] at e4
  rw [memK_sound hm 1 (by norm_num)] at e5
  exact ⟨e4, e5, h4, h5⟩

theorem c_mem {k : ℕ} (hk : k = 4 ∨ k = 5) {u : GL12} (hu : vm u = pkMat3 (ys.getD k 0)) :
    u ∈ Certificates.Cert25002.AB ⊓ Subgroup.centralizer (lsub qL 3 : Set GL12) := by
  obtain ⟨⟨hc4, w4, hw4, hv4⟩, ⟨hc5, w5, hw5, hv5⟩, h4, h5⟩ := c_facts
  rcases hk with rfl | rfl
  · rw [vm_inj (hu.trans hv4.symm)]
    exact ⟨hw4, (cen_iff invs.2.2.2.2.1 hc4 hv4.symm).2 h4⟩
  · rw [vm_inj (hu.trans hv5.symm)]
    exact ⟨hw5, (cen_iff invs.2.2.2.2.1 hc5 hv5.symm).2 h5⟩

theorem letY : LetIn (lsub gs 4 ⊔
    (Certificates.Cert25002.AB ⊓ Subgroup.centralizer (lsub qL 3 : Set GL12))) ys yis :=
  letIn_of invs.2.2.2.2.2 fun k hk u hu => by
    rcases lt_or_ge k 4 with h4 | h4
    · have e : ys.getD k 0 = gs.getD k 0 := by
        have := allBelow_eq ys_true k h4
        simpa only [Nat.beq_eq] using this
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨k, h4, by rw [hu, e]⟩)
    · exact Subgroup.mem_sup_right (c_mem (by omega) hu)

theorem canon_cover {i : ℕ} (hi : i < 7) : canonB (coverGS.mats.getD i oneM) = true := by
  have h := coverCheck_true
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h9, -⟩, hcan⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have e : coverGS.mats.getD i oneM = coverMats.getD i oneM := by
    change (coverMats.extract 0 7).getD i oneM = _
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, h9, Nat.zero_add,
      Nat.sub_zero]
    rw [if_pos (by omega)]
  rw [e]
  exact hcan i (by omega)

theorem pk_cover {i : ℕ} (hi : i < 7) :
    pkMat3 (lanesL (cgL i)) = ofMt (coverGS.mats.getD i oneM) := by
  have hc := canon_cover hi
  rw [coverGS_getD hi] at hc
  have hlen : (cgL i).length = 144 := by
    have hc' := hc
    simp only [canonB, Bool.and_eq_true, beq_iff_eq, List.size_toArray] at hc'
    exact hc'.1
  rw [coverGS_getD hi, ← pkMat3_lanesMt hc, lanesMt_toArray hlen]

theorem cover_mem {i : ℕ} (hi : i < 7) {u : GL12} (hu : vm u = ofMt (coverGS.mats.getD i oneM)) :
    u ∈ lsub gs 4 ⊔ (Certificates.Cert25002.AB ⊓ Subgroup.centralizer (lsub qL 3 : Set GL12)) := by
  obtain ⟨-, w, hw, hwv⟩ := evalL_in letY (wy.getD i [])
  rw [memK_sound wy_true i hi] at hwv
  rw [vm_inj (hu.trans ((pk_cover hi).symm.trans hwv.symm))]
  exact hw

open Certificates in
open CFSG.EvenSporadicStandard.TwoSuz Cert25002 in
theorem cert : Nat.card (⁅⁅S, S⁆, S⁆ : Subgroup GL12) = 2 ^ 7 ∧
    Nat.card (⁅⁅S, S⁆, S⁆ ⊓
      Subgroup.centralizer ((⁅⁅S, S⁆, S⁆ : Subgroup GL12) : Set GL12) : Subgroup GL12) = 32 ∧
    (∀ x ∈ (⁅⁅S, S⁆, S⁆ ⊓
      Subgroup.centralizer ((⁅⁅S, S⁆, S⁆ : Subgroup GL12) : Set GL12) : Subgroup GL12),
      x * x = 1) ∧
    ∃ Q : Subgroup GL12, Q ≤ S ∧ (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ (∀ x ∈ Q, x * x = 1) ∧
      Nat.card Q = 8 ∧ ∀ i < 7, ∀ u : GL12, vm u = ofMt (coverGS.mats.getD i oneM) →
        u ∈ S ⊔ (AB ⊓ Subgroup.centralizer (Q : Set GL12)) := by
  rw [S_eq, gamma3]
  exact ⟨card_n3, card_z, sq_z, lsub qL 3, q_le, q_comm, fun x hx => (q_all x hx).2, q_card,
    fun _ hi _ hu => cover_mem hi hu⟩

end CertificateChecks.KernelF21379102
