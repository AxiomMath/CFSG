module

public import Certificates.Kernel.U62Q.Checks
public import Certificates.Kernel.T46K.Chain
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Fischer.T46
public import CFSG.Perm.ChainSift

public section

namespace CertificateChecks.KernelU62Q

open CFSG.Open CFSG.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PC CFSG.KC.BfsPin CFSG.KC.B3S3K CFSG.KC.U62Q
  CertificateChecks.KernelT46

theorem szW : szOK 693 10 = true := by decide +kernel

theorem ng3 : EQ.ng = 3 := Nat.eq_of_beq_eq_true szQ.1

theorem okQ : bfsK 693 10 EQ.ng EQ.G EQ.N EQ.T EQ.E EQ.S = true :=
  bfsK_of_slices (L := 81) (K := 9) (C := EQ.C) (by decide) (by norm_num) szW EQ.g EQ.csAll EQ.t0
    EQ.dist (Nat.eq_of_beq_eq_true EQ.c0) (Nat.eq_of_beq_eq_true EQ.cK) EQ.rsAll

@[expose] noncomputable def gsQ : Array (Array ℕ) := Array.ofFn (n := 3) fun k => unpack 693 10 (EQ.G k)

noncomputable abbrev Q : Subgroup (Equiv.Perm (Fin 693)) := Subgroup.closure (permsA 693 gsQ)

theorem gsQ_size : gsQ.size = 3 := by simp [gsQ]

theorem gsQ_get {k : ℕ} (hk : k < 3) : gsQ[k]! = unpack 693 10 (EQ.G k) := by
  rw [getElem!_pos gsQ k (by rw [gsQ_size]; exact hk)]
  simp [gsQ]

theorem pGQ : ∀ k < EQ.ng, CFSG.KC.Misc.ArrEnum.permB 693 10 (EQ.G k) = true := fun k hk =>
  Orb.allN_iff.1 pG k (by rw [ng3] at hk; exact hk)

theorem ppG {k : ℕ} (hk : k < 3) : PP 693 10 (EQ.G k) :=
  CFSG.KC.Misc.ArrEnum.pp_of_permB szW (pGQ k (by rw [ng3]; exact hk))

theorem bindQ : BindA 693 10 gsQ EQ.ng EQ.G :=
  ⟨by rw [gsQ_size, ng3], fun j hj => gsQ_get (by rw [ng3] at hj; exact hj)⟩

theorem base_lt : ∀ p ∈ t46Base.toList, p < 693 := by
  intro p hp
  simp [t46Base] at hp
  omega

theorem enumQ : enumOK 693 gsQ t46Base.toList (enumBfs 693 gsQ t46Base.toList 800) = true ∧
    (enumBfs 693 gsQ t46Base.toList 800).pts.size = EQ.N ∧
    ∀ i < EQ.N, (enumBfs 693 gsQ t46Base.toList 800).pts[i]! = unpack 693 10 (EQ.T i) :=
  enum_of bindQ pGQ okQ base_lt EQ.keys (by rw [Nat.eq_of_beq_eq_true szQ.2]; norm_num)

theorem card_Q : Nat.card Q = 729 := by
  rw [(enumOK_spec base_lt enumQ.1).2.1, enumQ.2.1, Nat.eq_of_beq_eq_true szQ.2]

theorem gen_lt {k : ℕ} (hk : k < 3) : ∀ x ∈ gsQ[k]!, x < 693 := by
  intro x hx
  rw [gsQ_get hk] at hx
  unfold unpack at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact (ppG hk).2.1 i.val i.isLt

theorem gen_list {k : ℕ} (hk : k < 3) :
    gsQ[k]!.toList = mapK (pg 10 (mask 10) (EQ.G k)) QT := by
  rw [gsQ_get hk, mapK_eq, QT_eq]
  unfold unpack
  rw [Array.toList_ofFn]
  apply List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
  intro i h1 h2
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]

theorem gen_sift {k : ℕ} (hk : k < 3) :
    sift (t46Trees ()) (t46Letters ()) t46Base (t46Q ()) 0 gsQ[k]! = true := by
  have ht : t46Trees () = trees 693 5 CNTT PTST POST PART LABT := KernelT46.chain_eq.1
  rw [ht, sift_eq KernelT46.chain_hyp 5 0 rfl _ (gen_lt hk), gen_list hk]
  exact Orb.allN_iff.1 siftQ k hk

theorem gen_valid {k : ℕ} (hk : k < 3) : validA 693 gsQ[k]! = true := by
  rw [gsQ_get hk]
  exact validA_of (pGQ k (by rw [ng3]; exact hk))

theorem Q_le_T46 : Q ≤ CFSG.Fischer.T46 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk3 : k < 3 := by
    rw [Set.mem_setOf_eq, gsQ_size] at hk
    exact hk
  have hsz : gsQ[k]!.size = (t46Q ()).size := by
    rw [gsQ_get hk3]
    simp [t46Q, unpack]
  have hdom : ∀ t < (t46Q ()).size, (gsQ[k]!)[t]! = idx 693 (permOfArr 693 gsQ[k]!) ((t46Q ())[t]!) := by
    intro t ht
    have ht' : t < 693 := by simpa [t46Q] using ht
    rw [t46Q_get ht', idx_of_lt _ ht']
    exact (rep_of_validA (gen_valid hk3)).apply ht'
  exact chain_sift_mem rep_t46Letters t46_sep localCert_parts.2.1 hsz hdom (gen_sift hk3)

@[expose] noncomputable def wP (u : List (Fin 3)) : Equiv.Perm (Fin 693) :=
  (u.map fun x => permOfArr 693 gsQ[x.val]!).prod

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem rep_unpack {p : ℕ} (hp : PP 693 10 p) : Rep 693 (unpack 693 10 p) (permOfArr 693 (unpack 693 10 p)) :=
  rep_of_validA (validA_of (CFSG.KC.Misc.ArrEnum.permB_of_pp hp))

theorem rep_wK : ∀ u : List (Fin 3), Rep 693 (unpack 693 10 (wK EQ.G u)) (wP u) ∧ PP 693 10 (wK EQ.G u)
  | [] => by
    refine ⟨?_, PP.id szW⟩
    have h : wK EQ.G [] = pidn 693 10 := rfl
    rw [h, ← idA_eq szW]
    exact rep_idA
  | x :: u => by
    obtain ⟨h1, h2⟩ := rep_wK u
    have hx := ppG x.isLt
    have h : wK EQ.G (x :: u) = pcomp 693 10 (mask 10) (EQ.G x.val) (wK EQ.G u) := rfl
    have hw : wP (x :: u) = permOfArr 693 gsQ[x.val]! * wP u := by
      simp [wP]
    refine ⟨?_, h ▸ hx.mul h2⟩
    rw [h, hw, ← compA_PP hx h2, gsQ_get x.isLt]
    exact rep_compA (rep_unpack hx) h1

theorem wP_mem (u : List (Fin 3)) : wP u ∈ Q := by
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
  exact Subgroup.subset_closure ⟨x.val, by rw [Set.mem_setOf_eq, gsQ_size]; exact x.isLt, rfl⟩

theorem eq_of_beq {p q : ℕ} {x y : Equiv.Perm (Fin 693)} (hp : PP 693 10 p) (hq : PP 693 10 q)
    (hx : Rep 693 (unpack 693 10 p) x) (hy : Rep 693 (unpack 693 10 q) y) (h : x = y) :
    Nat.beq p q = true := by
  rw [← eqA_PP hp hq]
  exact (eqA_iff hx hy).2 h

theorem cube_ne {u : List (Fin 3)} (hu : cubeBad EQ.G u = true) : wP u ^ 3 ≠ 1 := by
  intro h3
  obtain ⟨hr, hp⟩ := rep_wK u
  rw [cubeBad, strictB_eq] at hu
  have hc := (rep_compA hr (rep_compA hr hr))
  rw [compA_PP hp hp, compA_PP hp (hp.mul hp)] at hc
  have hid : Rep 693 (unpack 693 10 (pidn 693 10)) 1 := by
    rw [← idA_eq szW]
    exact rep_idA
  have e := eq_of_beq (hp.mul (hp.mul hp)) (PP.id szW) hc hid (by rw [← pow_three]; exact h3)
  rw [e] at hu
  exact Bool.noConfusion hu

theorem comm_ne {a b : List (Fin 3)} (hab : commBad EQ.G a b = true) : wP a * wP b ≠ wP b * wP a := by
  intro hc
  obtain ⟨ha, hpa⟩ := rep_wK a
  obtain ⟨hb, hpb⟩ := rep_wK b
  rw [commBad, strictB_eq, strictB_eq] at hab
  have h1 := rep_compA ha hb
  have h2 := rep_compA hb ha
  rw [compA_PP hpa hpb] at h1
  rw [compA_PP hpb hpa] at h2
  have e := eq_of_beq (hpa.mul hpb) (hpb.mul hpa) h1 h2 hc
  rw [e] at hab
  exact Bool.noConfusion hab

theorem dg_cast (a b d : ZMod 3) (x : Fin 3) :
    ((dg (9 * a.val + 3 * b.val + d.val) x : ℕ) : ZMod 3) = ![a, b, d] x := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hd := ZMod.val_lt d
  fin_cases x
  · have e : (9 * a.val + 3 * b.val + d.val) / 9 % 3 = a.val := by omega
    simp [dg, e]
  · have e : (9 * a.val + 3 * b.val + d.val) / 3 % 3 = b.val := by omega
    simp [dg, e]
  · have e : (9 * a.val + 3 * b.val + d.val) % 3 = d.val := by omega
    simp [dg, e]

theorem card_le_81_of_le_Q {F : Subgroup (Equiv.Perm (Fin 693))} (hFQ : F ≤ Q)
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 81 := by
  classical
  have hgmem : ∀ k (hk : k < 3), permOfArr 693 gsQ[k]! ∈ Q :=
    fun k hk => Subgroup.subset_closure ⟨k, by rw [Set.mem_setOf_eq, gsQ_size]; exact hk, rfl⟩
  let gel : Fin 3 → Q := fun k => ⟨permOfArr 693 gsQ[k.1]!, hgmem k.1 k.2⟩
  by_contra hlt
  push Not at hlt
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFp : IsPGroup 3 F := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hF.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  have hk5 : 5 ≤ k := by
    by_contra h5
    have h81 : Nat.card F ≤ 81 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 81 := by norm_num
    exact absurd hlt (not_lt.2 h81)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (show 3 ^ 5 ∣ Nat.card F by
    rw [hk]; exact pow_dvd_pow 3 hk5)
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup (Equiv.Perm (Fin 693)), H = K.map F.subtype := ⟨_, rfl⟩
  have hHcard : Nat.card H = 243 := by
    rw [hHdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective F), hK]
    norm_num
  have hHF : H ≤ F := by rw [hHdef]; exact Subgroup.map_subtype_le K
  have hHpow : ∀ x ∈ H, x ^ 3 = 1 := fun x hx => hF.2 x (hHF hx)
  have hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro a ha b hb
    have h := hF.1.1.comm ⟨a, hHF ha⟩ ⟨b, hHF hb⟩
    simpa using congrArg Subtype.val h
  have hHQ : H ≤ Q := hHF.trans hFQ
  have hHq : Nat.card (H.subgroupOf Q) = 243 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHQ).toEquiv, hHcard]
  have hidx : (H.subgroupOf Q).index = 3 := by
    have h1 := Subgroup.card_mul_index (H.subgroupOf Q)
    rw [hHq, card_Q] at h1
    omega
  haveI : (H.subgroupOf Q).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, card_Q]; norm_num)
  have hq3 : Nat.card (Q ⧸ H.subgroupOf Q) = 3 := by
    rw [← hidx]
    rfl
  haveI : IsCyclic (Q ⧸ H.subgroupOf Q) := isCyclic_of_prime_card hq3
  let φ0 : (Q ⧸ H.subgroupOf Q) ≃* Multiplicative (ZMod 3) :=
    mulEquivOfCyclicCardEq (by rw [hq3, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  let φ : Q →* Multiplicative (ZMod 3) := φ0.toMonoidHom.comp (QuotientGroup.mk' _)
  have hker : ∀ x : Q, φ x = 1 ↔ x ∈ H.subgroupOf Q := by
    intro x
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let w : Fin 3 → ZMod 3 := fun k => Multiplicative.toAdd (φ (gel k))
  let c : ℕ := 9 * (w 0).val + 3 * (w 1).val + (w 2).val
  have hc27 : c < 27 := by
    have := ZMod.val_lt (w 0)
    have := ZMod.val_lt (w 1)
    have := ZMod.val_lt (w 2)
    omega
  have hdg : ∀ x : Fin 3, ((dg c x : ℕ) : ZMod 3) = w x := by
    intro x
    rw [dg_cast]
    fin_cases x <;> rfl
  have hword : ∀ u : List (Fin 3), φ ⟨wP u, wP_mem u⟩ = Multiplicative.ofAdd ((eK c u : ℕ) : ZMod 3) := by
    intro u
    induction u with
    | nil =>
      have h1 : (⟨wP [], wP_mem []⟩ : Q) = 1 := Subtype.ext (by simp [wP])
      rw [h1, map_one]
      simp [eK]
    | cons x u ih =>
      have h1 : (⟨wP (x :: u), wP_mem (x :: u)⟩ : Q) = gel x * ⟨wP u, wP_mem u⟩ :=
        Subtype.ext (by simp [wP, gel])
      have h2 : eK c (x :: u) = dg c x + eK c u := rfl
      rw [h1, map_mul, ih, h2, Nat.cast_add, ofAdd_add, hdg x]
      rfl
  have hmem : ∀ u : List (Fin 3), orthK c u = true → wP u ∈ H := by
    intro u hu
    have h0 : eK c u % 3 = 0 := Nat.eq_of_beq_eq_true hu
    have h1 : φ ⟨wP u, wP_mem u⟩ = 1 := by
      rw [hword, ← ZMod.natCast_mod, h0]
      simp
    exact Subgroup.mem_subgroupOf.1 ((hker _).1 h1)
  have hwit := witQ
  rw [witK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hwit
  have hcov := Orb.allN_iff.1 coverQ c hc27
  rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true] at hcov
  rcases hcov with ⟨u, hu, ho⟩ | ⟨e, he, ho⟩
  · exact cube_ne (hwit.1 u hu) (hHpow _ (hmem u ho))
  · rw [Bool.and_eq_true] at ho
    exact comm_ne (hwit.2 e he) (hHcomm _ (hmem _ ho.1) _ (hmem _ ho.2))

theorem sylow_main :
    ∃ Q : Subgroup (Equiv.Perm (Fin 693)), Q ≤ CFSG.Fischer.T46 ∧ Nat.card Q = 729 ∧
      ∀ E : Subgroup (Equiv.Perm (Fin 693)), E ≤ Q → IsElemAbelian 3 E → Nat.card E ≤ 81 :=
  ⟨Q, Q_le_T46, card_Q, fun _ hE hab => card_le_81_of_le_Q hE hab⟩

end CertificateChecks.KernelU62Q

end
