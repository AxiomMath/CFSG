module

public import Certificates.Kernel.Sporadic.M22Syl.Fib
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Certificates.Kernel.Spor.MSylowSound
public import CFSG.Certificates.Kernel.Spor.MSylowSoundW
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Derivs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M22
public meta import CFSG.Monster.B.Mathieu.M22Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PCountW
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CertificateChecks.KernelSpor.M22Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native

set_option maxRecDepth 100000

@[expose] def z0 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 5] * List.formPerm [2, 11] * List.formPerm [3, 15] * List.formPerm [4, 18] *
    List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [12, 21] *
    List.formPerm [19, 20]

theorem natTbl_z0 : natTbl 22 m22SylowZ = toTable z0 := by
  have h : ∀ i : Fin 22, UInt32.ofNat (m22SylowZ.getD i.val 0) = UInt32.ofNat (z0 i).val := by
    decide +kernel
  unfold natTbl toTable
  exact congrArg _ (funext h)

theorem pk_one : pkw 5 (1 : Equiv.Perm (Fin 22)) = I := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_a : pkw 5 m22gA = A := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_ai : pkw 5 m22gA⁻¹ = Ai := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_b : pkw 5 m22gB = B := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_bi : pkw 5 m22gB⁻¹ = Bi := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_z : pkw 5 z0 = Z := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_zi : pkw 5 z0⁻¹ = Zi := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_zb : pkw 5 (z0 * m22gB * z0⁻¹) = ZB := Nat.eq_of_beq_eq_true (by quickRfl)

@[expose] def lv : List (List (Equiv.Perm (Fin 22))) :=
  (List.finRange m22Certificate.baseCount).map (levelTransversals m22Certificate)

theorem lv_pk : (lv.map fun T => T.map (pkw 5)) = [L0, L1, L2, L3, L4] := by decide +kernel

theorem pt_eq : exprsV 22 5 (mask 5) I (slpP 22 5 (mask 5) I A Ai B Bi m22Derivs) ES = PT :=
  eq_of_beq pt

theorem len_L0 : L0.length = 22 := by decide +kernel

theorem mem_of_nodup_card {M : Type*} [Finite M] {p : M → Prop} {L : List M} (hL : L.Nodup)
    (hLp : ∀ x ∈ L, p x) (hc : Nat.card {x // p x} ≤ L.length) : ∀ x, p x → x ∈ L := by
  classical
  intro x hx
  by_contra hxL
  have hnd : (x :: L).Nodup := List.nodup_cons.2 ⟨hxL, hL⟩
  have hsub : ∀ y ∈ x :: L, p y := by
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact hLp y hy
  have : Fintype {y // p y} := Fintype.ofFinite _
  have h1 := (List.Nodup.pmap (f := fun y hy => (⟨y, hy⟩ : {y // p y})) (H := hsub)
    (fun _ _ _ _ h => congrArg Subtype.val h) hnd).length_le_card
  rw [List.length_pmap, List.length_cons, ← Nat.card_eq_fintype_card] at h1
  omega

def FibP {M : Type*} [Group M] (x y : M) : Prop :=
  orderOf y = 4 ∧ orderOf (x * y) = 11 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 6

theorem fibP_conj {M : Type*} [Group M] (g x y : M) :
    FibP (g * x * g⁻¹) (g * y * g⁻¹) ↔ FibP x y := by
  have e : ∀ u : M, orderOf (g * u * g⁻¹) = orderOf u := fun u => by
    rw [← MulAut.conj_apply]
    exact MulEquiv.orderOf_eq _ u
  have h1 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  have h2 : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
      g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ := by group
  unfold FibP
  rw [h2, h1, e, e, e]

theorem fibP_coe {G : Type*} [Group G] {H : Subgroup G} (x y : H) :
    FibP x y ↔ FibP (x : G) (y : G) := by
  simp only [FibP, ← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv]

theorem fib_cover {M : Type*} [Group M] [Finite M] (a : M) {L : List M} (hL : L.Nodup)
    (hLa : ∀ y ∈ L, FibP a y) (hinv : ∀ x : M, orderOf x = 2 → ∃ g, x = g * a * g⁻¹)
    (hcount : Nat.card {p : M × M // orderOf p.1 = 2 ∧ FibP p.1 p.2} ≤
      Nat.card {x : M // orderOf x = 2} * L.length)
    (hpos : 0 < Nat.card {x : M // orderOf x = 2}) :
    ∀ y, FibP a y → y ∈ L := by
  classical
  refine mem_of_nodup_card hL hLa ?_
  choose g hg using hinv
  have key : ∀ x c : M, x = c * a * c⁻¹ → ∀ y, FibP a y → FibP x (c * y * c⁻¹) := by
    rintro x c rfl y hy
    exact (fibP_conj c a y).2 hy
  let f : {x : M // orderOf x = 2} × {y // FibP a y} →
      {p : M × M // orderOf p.1 = 2 ∧ FibP p.1 p.2} := fun q =>
    ⟨(q.1.1, g q.1.1 q.1.2 * q.2.1 * (g q.1.1 q.1.2)⁻¹), q.1.2,
      key _ _ (hg q.1.1 q.1.2) _ q.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ h
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have h3 : y = y' := mul_left_cancel (mul_right_cancel h2)
    subst h3
    rfl
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at h1
  exact Nat.le_of_mul_le_mul_left (h1.trans hcount) hpos

@[expose] def ca1M : NativeSporadic.M22 :=
  m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹

@[expose] def ca2M : NativeSporadic.M22 :=
  m22b⁻¹ * m22a * m22b * m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22b *
    m22a * m22b * m22a * m22b * m22a * m22b * m22b

@[expose] def fr2M : NativeSporadic.M22 :=
  m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b * m22b

@[expose] def fr3M : NativeSporadic.M22 :=
  m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22b

@[expose] def ca1 : Equiv.Perm (Fin 22) := ca1M
@[expose] def ca2 : Equiv.Perm (Fin 22) := ca2M
@[expose] def fr2 : Equiv.Perm (Fin 22) := fr2M
@[expose] def fr3 : Equiv.Perm (Fin 22) := fr3M

theorem pk_ca1 : pkw 5 ca1 = CA1 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_ca1i : pkw 5 ca1⁻¹ = CA1i := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_ca2 : pkw 5 ca2 = CA2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_ca2i : pkw 5 ca2⁻¹ = CA2i := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_fr2 : pkw 5 fr2 = FR2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_fr3 : pkw 5 fr3 = FR3 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem gA_mem : m22gA ∈ NativeSporadic.M22 := m22a.2
theorem gB_mem : m22gB ∈ NativeSporadic.M22 := m22b.2

theorem ca1_mem : ca1 ∈ NativeSporadic.M22 := ca1M.2
theorem ca2_mem : ca2 ∈ NativeSporadic.M22 := ca2M.2
theorem fr2_mem : fr2 ∈ NativeSporadic.M22 := fr2M.2
theorem fr3_mem : fr3 ∈ NativeSporadic.M22 := fr3M.2

theorem ca1_comm : ca1 * m22gA = m22gA * ca1 := by decide +kernel
theorem ca2_comm : ca2 * m22gA = m22gA * ca2 := by decide +kernel
theorem gA_inv : m22gA⁻¹ = m22gA := by decide +kernel

theorem ord_of {x : Equiv.Perm (Fin 22)} {n : Nat} (hn : 0 < n)
    (h : x ^ n = 1 ∧ ∀ m < n, 0 < m → x ^ m ≠ 1) : orderOf x = n :=
  (orderOf_eq_iff hn).2 h

theorem fibP_b : FibP m22gA m22gB :=
  ⟨ord_of (by norm_num) (by decide +kernel), ord_of (by norm_num) (by decide +kernel),
    ord_of (by norm_num) (by decide +kernel)⟩
theorem fibP_bi : FibP m22gA m22gB⁻¹ :=
  ⟨ord_of (by norm_num) (by decide +kernel), ord_of (by norm_num) (by decide +kernel),
    ord_of (by norm_num) (by decide +kernel)⟩
theorem fibP_fr2 : FibP m22gA fr2 :=
  ⟨ord_of (by norm_num) (by decide +kernel), ord_of (by norm_num) (by decide +kernel),
    ord_of (by norm_num) (by decide +kernel)⟩
theorem fibP_fr3 : FibP m22gA fr3 :=
  ⟨ord_of (by norm_num) (by decide +kernel), ord_of (by norm_num) (by decide +kernel),
    ord_of (by norm_num) (by decide +kernel)⟩

section

attribute [local irreducible] ca1 ca2

theorem cl_ca {c : Equiv.Perm (Fin 22)} (hc : c ∈ Subgroup.closure {ca1, ca2}) :
    c ∈ NativeSporadic.M22 ∧ c * m22gA = m22gA * c := by
  have h1 : Subgroup.closure {ca1, ca2} ≤ NativeSporadic.M22 := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨ca1_mem, ca2_mem⟩
  have h2 : Subgroup.closure {ca1, ca2} ≤ Subgroup.centralizer {m22gA} := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨ca1_comm, ca2_comm⟩
  exact ⟨h1 hc, Subgroup.mem_centralizer_singleton_iff.1 (h2 hc)⟩

end

theorem fibOrb_ok {r : Equiv.Perm (Fin 22)} (hr : r ∈ NativeSporadic.M22) (hF : FibP m22gA r) :
    ∀ k ∈ fibOrb (pkw 5 r), ∃ y, k = pkw 5 y ∧ y ∈ NativeSporadic.M22 ∧ FibP m22gA y := by
  have hw : (22 : Nat) ≤ 2 ^ 5 := by norm_num
  have hn32 : (22 : Nat) < 2 ^ 32 := by norm_num
  have h := (conjDFS_mem_w hw hn32 (Subgroup.closure {ca1, ca2})
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) (ρ := r) 384).2
  rw [pk_ca1, pk_ca1i, pk_ca2, pk_ca2i] at h
  intro k hk
  obtain ⟨c, hc, rfl⟩ := h k hk
  obtain ⟨hcM, hca⟩ := cl_ca hc
  refine ⟨_, rfl, mul_mem (mul_mem hcM hr) (inv_mem hcM), ?_⟩
  have e : c * m22gA * c⁻¹ = m22gA := by rw [hca, mul_inv_cancel_right]
  rw [← fibP_conj c, e] at hF
  exact hF

theorem yf_ok : ∀ k ∈ Yf, ∃ y, k = pkw 5 y ∧ y ∈ NativeSporadic.M22 ∧ FibP m22gA y := by
  have h := eq_of_beq yf_eq
  intro k hk
  rw [← h] at hk
  simp only [List.mem_append] at hk
  rcases hk with ((hk | hk) | hk) | hk
  · exact fibOrb_ok gB_mem fibP_b k (pk_b ▸ hk)
  · exact fibOrb_ok (inv_mem gB_mem) fibP_bi k (pk_bi ▸ hk)
  · exact fibOrb_ok fr2_mem fibP_fr2 k (pk_fr2 ▸ hk)
  · exact fibOrb_ok fr3_mem fibP_fr3 k (pk_fr3 ▸ hk)

theorem inv_len : Nat.beq (conjDFS 22 5 (mask 5) A Ai B Bi A 1155).length 1155 = true := by
  quickRfl

theorem inv_conj : ∀ x : NativeSporadic.M22, orderOf x = 2 → ∃ g, x = g * m22a * g⁻¹ := by
  have hw : (22 : Nat) ≤ 2 ^ 5 := by norm_num
  have hn32 : (22 : Nat) < 2 ^ 32 := by norm_num
  have h := conjDFS_mem_w hw hn32 NativeSporadic.M22 gA_mem gB_mem (ρ := m22gA) 1155
  rw [pk_a, pk_ai, pk_b, pk_bi] at h
  generalize hKd : conjDFS 22 5 (mask 5) A Ai B Bi A 1155 = K at h
  obtain ⟨hnd, hK⟩ := h
  obtain ⟨hc, hpk⟩ := upkw_conj hw hK
  have hmem : ∀ y ∈ K.map (upkw 22 5), y ∈ NativeSporadic.M22 := by
    intro y hy
    obtain ⟨c, hcM, rfl⟩ := hc y hy
    exact mul_mem (mul_mem hcM gA_mem) (inv_mem hcM)
  let L : List NativeSporadic.M22 := (K.map (upkw 22 5)).pmap Subtype.mk hmem
  have hLnd : L.Nodup := by
    have h1 : (K.map (upkw 22 5)).Nodup := by
      rw [← hpk] at hnd
      exact hnd.of_map _
    exact h1.pmap fun _ _ _ _ h => congrArg Subtype.val h
  obtain ⟨ha, -, -, -, h2, -⟩ := at_m22_image_pair_count
  have ha' : orderOf m22gA = 2 := (Subgroup.orderOf_coe m22a).trans ha
  have hLo : ∀ x ∈ L, orderOf x = 2 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_pmap.1 hx
    obtain ⟨c, hcM, rfl⟩ := hc y hy
    have e1 : orderOf (c * m22gA * c⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact ha'
    exact (Subgroup.orderOf_coe _).symm.trans e1
  have hlen : L.length = 1155 := by
    rw [List.length_pmap, List.length_map, ← hKd]
    exact Nat.eq_of_beq_eq_true inv_len
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_pmap.1 (mem_of_nodup_card hLnd hLo (by rw [h2, hlen]) x hx)
  obtain ⟨c, hcM, rfl⟩ := hc y hy
  exact ⟨⟨c, hcM⟩, rfl⟩

theorem yf_cover : ∀ y ∈ NativeSporadic.M22, FibP m22gA y → pkw 5 y ∈ Yf := by
  have hw : (22 : Nat) ≤ 2 ^ 5 := by norm_num
  have hup : ∀ y ∈ Yf.map (upkw 22 5), pkw 5 y ∈ Yf ∧ y ∈ NativeSporadic.M22 ∧ FibP m22gA y := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    obtain ⟨y', rfl, hy'⟩ := yf_ok k hk
    rw [upkw_pkw hw]
    exact ⟨hk, hy'⟩
  let L : List NativeSporadic.M22 := (Yf.map (upkw 22 5)).pmap Subtype.mk fun y hy => (hup y hy).2.1
  have hLnd : L.Nodup := by
    have h1 : (Yf.map (upkw 22 5)).Nodup := by
      refine (nodup_of_distB yf_dist).map_on fun k hk k' hk' he => ?_
      obtain ⟨y, rfl, -⟩ := yf_ok k hk
      obtain ⟨y', rfl, -⟩ := yf_ok k' hk'
      rw [upkw_pkw hw, upkw_pkw hw] at he
      rw [he]
    exact h1.pmap fun _ _ _ _ h => congrArg Subtype.val h
  have hLa : ∀ y ∈ L, FibP m22a y := by
    intro y hy
    obtain ⟨y', hy', rfl⟩ := List.mem_pmap.1 hy
    exact (fibP_coe _ _).2 (hup y' hy').2.2
  have hlen : L.length = 1536 := by
    rw [List.length_pmap, List.length_map]
    exact yf_len
  obtain ⟨-, -, -, -, h2, -, hT⟩ := at_m22_image_pair_count
  have hT' : Nat.card {p : NativeSporadic.M22 × NativeSporadic.M22 //
      orderOf p.1 = 2 ∧ FibP p.1 p.2} = 1774080 := hT
  intro y hy hF
  have hm := fib_cover m22a hLnd hLa inv_conj (by rw [hT', h2, hlen]) (by rw [h2]; norm_num)
    ⟨y, hy⟩ ((fibP_coe _ _).2 hF)
  obtain ⟨y', hy', he⟩ := List.mem_pmap.1 hm
  have he' : y' = y := congrArg Subtype.val he
  subst he'
  exact (hup _ hy').1

theorem facts : (sylowAutOK 22 (toTable m22gA) (toTable m22gB) m22Derivs
      m22SylowExprs (natTbl 22 m22SylowZ) 150 443520 7 = true)
    ∧ (survivorsOK 22 (toTable m22gA) (toTable m22gB) (natTbl 22 m22SylowZ)
      m22Derivs m22SylowExprs 11 6 4 (orderTables m22Certificate 4) = true) := by
  have hn32 : (22 : Nat) < 2 ^ 32 := by norm_num
  have hw : (22 : Nat) ≤ 2 ^ 5 := by norm_num
  have hes : m22SylowExprs = ES := rfl
  rw [natTbl_z0, hes]
  refine ⟨sylowAutP_sound_w hn32 hw m22gA m22gB z0 m22Derivs ES 150 443520 7 ?_,
    survF_sound_cond_w hn32 hw m22Certificate m22gA m22gB z0 m22Derivs ES (by norm_num)
      (by norm_num) (by norm_num) ?_⟩
  · rw [pk_one, pk_a, pk_ai, pk_b, pk_bi, pk_z, pk_zi]
    exact syl
  · rw [pk_one, pk_a, pk_ai, pk_b, pk_bi, pk_zb, pt_eq]
    intro g hg h4 h11 h6
    rw [mem_enumeration_iff _ m22Certificate_check, m22Certificate_originalSubgroup] at hg
    exact yf_surv _ (yf_cover g hg ⟨h4, h11, by rwa [gA_inv]⟩)

end CertificateChecks.KernelSpor.M22Syl

end
