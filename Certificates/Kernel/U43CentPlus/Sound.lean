module

public import Certificates.Kernel.U43CentPlus.Checks
public import Certificates.Kernel.U43Mod.Glue
public import CFSG.Certificates.Kernel.Spor.PK.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.OutU43Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.Schreier.ONArrayDatum
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43CentPlus

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43CentPlus CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KS.U43Mod CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43
  CertificateChecks.KernelU43Mod Subgroup

@[expose] noncomputable def pkP (p : ℕ) : Equiv.Perm (Fin 820) := permOfArr 820 (unpack 820 10 p)

theorem rep_pkP {p p' : ℕ} (h : permOK 820 10 (mask 10) (820 * 10) p p' = true) :
    Rep 820 (unpack 820 10 p) (pkP p) ∧ Rep 820 (unpack 820 10 p') (pkP p)⁻¹ :=
  rep_permOfArr (isInvA_unpack h)

theorem pkP_apply {p p' : ℕ} (h : permOK 820 10 (mask 10) (820 * 10) p p' = true) (q : ℕ)
    (hq : q < 820) : pg 10 (mask 10) p q = (pkP p ⟨q, hq⟩ : ℕ) := by
  rw [← unpack_get hq]
  exact (rep_pkP h).1 ⟨q, hq⟩

theorem pkP_inv_apply {p p' : ℕ} (h : permOK 820 10 (mask 10) (820 * 10) p p' = true) (q : ℕ)
    (hq : q < 820) : pg 10 (mask 10) p' q = ((pkP p)⁻¹ ⟨q, hq⟩ : ℕ) := by
  rw [← unpack_get hq]
  exact (rep_pkP h).2 ⟨q, hq⟩

theorem pkP_mem {p p' : ℕ}
    (h : permOK 820 10 (mask 10) (820 * 10) p p' = true) (hs : inPU p = true) : pkP p ∈ P := by
  have hr : allN 820 (fun i => Nat.blt (pg 10 (mask 10) p i) 820) = true :=
    CFSG.KS.PackFld.allN_of_forall fun i hi => by
      rw [← unpack_get hi]
      exact Nat.blt_eq.mpr ((rep_pkP h).1.lt hi)
  have hs := siftK_sound binds perm C.hl rfl hr hs
  rw [← base_eq] at hs
  exact (inP_iff (rep_pkP h).1).1 hs

theorem incK_lt {n : ℕ} {K : ℕ → ℕ} (h : incK n K = true) {i j : ℕ} (hij : i < j) (hj : j < n) :
    K i < K j := by
  have hs := allN_spec h
  induction j with
  | zero => omega
  | succ j ih =>
    have hn : j < Nat.sub n 1 := by
      change j < n - 1
      omega
    have h1 : K j < K (j + 1) := Nat.blt_eq.mp (hs j hn)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h2 | h2
    · exact (ih h2 (by omega)).trans h1
    · rw [h2]
      exact h1

theorem incK_inj {n : ℕ} {K : ℕ → ℕ} (h : incK n K = true) {i j : ℕ} (hi : i < n) (hj : j < n)
    (e : K i = K j) : i = j := by
  rcases lt_trichotomy i j with hl | hl | hl
  · exact absurd e (ne_of_lt (incK_lt h hl hj))
  · exact hl
  · exact absurd e.symm (ne_of_lt (incK_lt h hl hi))

theorem bKey_eq {x : Equiv.Perm (Fin 820)} {f f' : ℕ → ℕ}
    (hf : ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ))
    (hf' : ∀ q (hq : q < 820), f' q = (x ⟨q, hq⟩ : ℕ)) : bKey f = bKey f' := by
  have e : ∀ q, q < 820 → f q = f' q := fun q hq => by rw [hf q hq, hf' q hq]
  unfold bKey
  rw [e (nat_lit 0) (by decide), e (nat_lit 1) (by decide), e (nat_lit 9) (by decide)]

theorem inj_of_incK {n : ℕ} {F : ℕ → ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin 820)}
    (hF : ∀ i < n, ∀ q (hq : q < 820), F i q = (g i ⟨q, hq⟩ : ℕ))
    (h : incK n (fun i => bKey (F i)) = true) {i j : ℕ} (hi : i < n) (hj : j < n)
    (e : g i = g j) : i = j :=
  incK_inj h hi hj (bKey_eq (hF i hi) (fun q hq => by rw [hF j hj q hq, e]))

theorem inv_mem_of_mul {S : Set (Equiv.Perm (Fin 820))} (h1 : (1 : Equiv.Perm (Fin 820)) ∈ S)
    (hm : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) {x : Equiv.Perm (Fin 820)} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpow : ∀ n : ℕ, x ^ n ∈ S := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ']
      exact hm _ hx _ ih
  have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]
  rw [hinv]
  exact hpow _

theorem kE_spec {i : ℕ} (hi : i < 4) :
    permOK 820 10 (mask 10) (820 * 10) (ET i) (ETI i) = true ∧ inPU (ET i) = true ∧
      baseEq bs (GE i) (GM i) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kE i hi)
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  exact ⟨h1, h2, h3⟩

theorem kQ_spec {j : ℕ} (hj : j < 32) :
    permOK 820 10 (mask 10) (820 * 10) (QT j) (QTI j) = true ∧ inPU (QT j) = true ∧
      commA (GQ j) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kQ j hj)
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  exact ⟨h1, h2, h3⟩

theorem kT_spec0 : Nat.beq (TT 0) (pidn 820 10) = true := by
  have h := kT
  rw [Bool.and_eq_true] at h
  exact h.1

theorem kT_spec {k : ℕ} (hk : k < 4) :
    permOK 820 10 (mask 10) (820 * 10) (TT k) (TTI k) = true ∧ inPU (TT k) = true ∧
      commA (GT k) = true := by
  have h := kT
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec h.2 k hk)
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  exact ⟨h1, h2, h3⟩

@[expose] noncomputable def EP (i : ℕ) : Equiv.Perm (Fin 820) := pkP (ET i)

@[expose] noncomputable def QP (j : ℕ) : Equiv.Perm (Fin 820) := pkP (QT j)

@[expose] noncomputable def TP (k : ℕ) : Equiv.Perm (Fin 820) := pkP (TT k)

@[expose] noncomputable def CE (c : ℕ) : Equiv.Perm (Fin 820) :=
  QP (Nat.mod c 32) * TP (Nat.div c 32)

theorem GE_eq {i : ℕ} (hi : i < 4) (q : ℕ) (hq : q < 820) : GE i q = (EP i ⟨q, hq⟩ : ℕ) :=
  pkP_apply (kE_spec hi).1 q hq

theorem GQ_eq {j : ℕ} (hj : j < 32) (q : ℕ) (hq : q < 820) : GQ j q = (QP j ⟨q, hq⟩ : ℕ) :=
  pkP_apply (kQ_spec hj).1 q hq

theorem GT_eq {k : ℕ} (hk : k < 4) (q : ℕ) (hq : q < 820) : GT k q = (TP k ⟨q, hq⟩ : ℕ) :=
  pkP_apply (kT_spec hk).1 q hq

theorem mod32_lt (c : ℕ) : Nat.mod c 32 < 32 := Nat.mod_lt c (by norm_num)

theorem div32_lt {c : ℕ} (hc : c < 128) : Nat.div c 32 < 4 := by
  change c / 32 < 4
  omega

theorem GC_eq {c : ℕ} (hc : c < 128) (q : ℕ) (hq : q < 820) : GC c q = (CE c ⟨q, hq⟩ : ℕ) := by
  change GQ (Nat.mod c 32) (GT (Nat.div c 32) q) = _
  rw [CE, Equiv.Perm.mul_apply, GT_eq (div32_lt hc) q hq, GQ_eq (mod32_lt c) _ (Fin.is_lt _),
    Fin.eta]

theorem pidn_base : baseEq bs (fun q => pg 10 (mask 10) (pidn 820 10) q) (fun q => q) = true := by
  quickRfl

theorem EP_mem {i : ℕ} (hi : i < 4) : EP i ∈ P := pkP_mem (kE_spec hi).1 (kE_spec hi).2.1

theorem QP_mem {j : ℕ} (hj : j < 32) : QP j ∈ P := pkP_mem (kQ_spec hj).1 (kQ_spec hj).2.1

theorem TP_mem {k : ℕ} (hk : k < 4) : TP k ∈ P := pkP_mem (kT_spec hk).1 (kT_spec hk).2.1

theorem CE_mem {c : ℕ} (hc : c < 128) : CE c ∈ P :=
  P.mul_mem (QP_mem (mod32_lt c)) (TP_mem (div32_lt hc))

theorem TP_zero : TP 0 = 1 := by
  have h1 : TT 0 = pidn 820 10 := Nat.eq_of_beq_eq_true kT_spec0
  have hb : baseEq bs (GT 0) (fun q => q) = true := by
    change baseEq bs (fun q => pg 10 (mask 10) (TT 0) q) (fun q => q) = true
    rw [h1]
    exact pidn_base
  exact eq_of_baseEq (TP_mem (by norm_num)) P.one_mem (GT_eq (by norm_num)) id_eq' hb

theorem EP_eq {i : ℕ} (hi : i < 4) : EP i = m4 i := by
  rw [m4_eq hi]
  exact eq_of_baseEq (EP_mem hi) (m5_mem i) (GE_eq hi) (GM_eq i) (kE_spec hi).2.2

theorem comm_of_commA {x : Equiv.Perm (Fin 820)} (hx : x ∈ P) {f : ℕ → ℕ}
    (hf : ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ)) (h : commA f = true) :
    x * CP 0 = CP 0 * x := by
  refine eq_of_baseEq (P.mul_mem hx (CP_mem (by norm_num))) (P.mul_mem (CP_mem (by norm_num)) hx)
    (f := fun q => f (GA 0 q)) (f' := fun q => GA 0 (f q)) (fun q hq => ?_) (fun q hq => ?_) h
  · rw [GA_eq (by norm_num) q hq, hf _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]
  · rw [hf q hq, GA_eq (by norm_num) _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]

theorem sq_of_rootA {x : Equiv.Perm (Fin 820)} (hx : x ∈ P) {f : ℕ → ℕ}
    (hf : ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ)) (h : rootA f = true) : x * x = CP 0 := by
  refine eq_of_baseEq (P.mul_mem hx hx) (CP_mem (by norm_num)) (f := fun q => f (f q))
    (fun q hq => ?_) (GA_eq (by norm_num)) h
  rw [hf q hq, hf _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]

theorem rootA_of_sq {x : Equiv.Perm (Fin 820)} {f : ℕ → ℕ}
    (hf : ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ)) (h : x * x = CP 0) : rootA f = true :=
  baseEq_of_eq (x := x * x) (y := CP 0) (fun q hq => by
    rw [hf q hq, hf _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]) (GA_eq (by norm_num)) h

section H4

theorem H4_eq : H4 = P ⊓ centralizer ({CP 0} : Set (Equiv.Perm (Fin 820))) :=
  Subgroup.eq_of_le_of_card_ge H4_le (by rw [card_H4, card_CA])

theorem mem_H4 {x : Equiv.Perm (Fin 820)} (hx : x ∈ P) (h : x * CP 0 = CP 0 * x) : x ∈ H4 := by
  rw [H4_eq]
  exact mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 h⟩

theorem comm_of_mem_H4 {x : Equiv.Perm (Fin 820)} (hx : x ∈ H4) : x * CP 0 = CP 0 * x := by
  rw [H4_eq] at hx
  exact mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2

theorem EP_mem_H4 {i : ℕ} (hi : i < 4) : EP i ∈ H4 := by
  rw [EP_eq hi]
  exact m4_mem_H4 hi

theorem QP_mem_H4 {j : ℕ} (hj : j < 32) : QP j ∈ H4 :=
  mem_H4 (QP_mem hj) (comm_of_commA (QP_mem hj) (GQ_eq hj) (kQ_spec hj).2.2)

theorem TP_mem_H4 {k : ℕ} (hk : k < 4) : TP k ∈ H4 :=
  mem_H4 (TP_mem hk) (comm_of_commA (TP_mem hk) (GT_eq hk) (kT_spec hk).2.2)

theorem CE_mem_H4 {c : ℕ} (hc : c < 128) : CE c ∈ H4 :=
  H4.mul_mem (QP_mem_H4 (mod32_lt c)) (TP_mem_H4 (div32_lt hc))

end H4

theorem QP_inj {i j : ℕ} (hi : i < 32) (hj : j < 32) (e : QP i = QP j) : i = j :=
  inj_of_incK (fun i hi => GQ_eq hi) kQinc hi hj e

@[expose] noncomputable def mtI (i j : ℕ) : ℕ := fld(MT i, Nat.mul 5 j, 31)

theorem kMT_spec {i j : ℕ} (hi : i < 32) (hj : j < 32) :
    mtI i j < 32 ∧ baseEq bs (fun q => GQ i (GQ j q)) (GQ (mtI i j)) = true := by
  have h := allN_spec (allN_spec kMT i hi) j hj
  rw [CFSG.KS.U43Mod.strictB_eq, bAnd_iff, blt_iff] at h
  exact h

theorem QP_mul {i j : ℕ} (hi : i < 32) (hj : j < 32) : QP i * QP j = QP (mtI i j) := by
  refine eq_of_baseEq (P.mul_mem (QP_mem hi) (QP_mem hj)) (QP_mem (kMT_spec hi hj).1)
    (f := fun q => GQ i (GQ j q)) (fun q hq => ?_) (GQ_eq (kMT_spec hi hj).1) (kMT_spec hi hj).2
  rw [GQ_eq hj q hq, GQ_eq hi _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]

theorem kIA_spec : IA 0 < 32 ∧ baseEq bs (GQ (IA 0)) (GA 0) = true := by
  have h := kIA
  rw [Bool.and_eq_true, blt_iff] at h
  exact h

theorem QP_IA : QP (IA 0) = CP 0 :=
  eq_of_baseEq (QP_mem kIA_spec.1) (CP_mem (by norm_num)) (GQ_eq kIA_spec.1)
    (GA_eq (by norm_num)) kIA_spec.2

theorem QS_mul {x y : Equiv.Perm (Fin 820)} (hx : x ∈ QP '' Set.Iio 32)
    (hy : y ∈ QP '' Set.Iio 32) : x * y ∈ QP '' Set.Iio 32 := by
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  exact ⟨mtI i j, (kMT_spec hi hj).1, (QP_mul hi hj).symm⟩

theorem QS_one : (1 : Equiv.Perm (Fin 820)) ∈ QP '' Set.Iio 32 := by
  have h := QS_mul ⟨IA 0, kIA_spec.1, rfl⟩ ⟨IA 0, kIA_spec.1, rfl⟩
  rwa [QP_IA, CP0_sq] at h

@[expose] noncomputable def Q0 : Subgroup (Equiv.Perm (Fin 820)) where
  carrier := QP '' Set.Iio 32
  mul_mem' := QS_mul
  one_mem' := QS_one
  inv_mem' := inv_mem_of_mul QS_one fun _ hx _ hy => QS_mul hx hy

theorem mem_Q0 {x : Equiv.Perm (Fin 820)} : x ∈ Q0 ↔ ∃ j < 32, QP j = x := Iff.rfl

theorem QP_mem_Q0 {j : ℕ} (hj : j < 32) : QP j ∈ Q0 := ⟨j, hj, rfl⟩

theorem a_mem_Q0 : CP 0 ∈ Q0 := QP_IA ▸ QP_mem_Q0 kIA_spec.1

theorem card_Q0 : Nat.card Q0 = 32 := by
  let f : Fin 32 → Q0 := fun j => ⟨QP j, QP_mem_Q0 j.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j e => Fin.ext (QP_inj i.2 j.2 (congrArg Subtype.val e)), ?_⟩
    rintro ⟨x, j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem kPI_spec {i j : ℕ} (hi : i < 4) (hj : j < 32) :
    GP i j < 32 ∧ baseEq bs (fun q => GE i (GQ j q)) (fun q => GQ (GP i j) (GE i q)) = true := by
  have h := allN_spec (allN_spec kPI i hi) j hj
  rw [CFSG.KS.U43Mod.strictB_eq, bAnd_iff, blt_iff] at h
  exact h

theorem EP_conj {i j : ℕ} (hi : i < 4) (hj : j < 32) :
    EP i * QP j * (EP i)⁻¹ = QP (GP i j) := by
  have h : EP i * QP j = QP (GP i j) * EP i := by
    refine eq_of_baseEq (P.mul_mem (EP_mem hi) (QP_mem hj))
      (P.mul_mem (QP_mem (kPI_spec hi hj).1) (EP_mem hi)) (f := fun q => GE i (GQ j q))
      (f' := fun q => GQ (GP i j) (GE i q)) (fun q hq => ?_) (fun q hq => ?_) (kPI_spec hi hj).2
    · rw [GQ_eq hj q hq, GE_eq hi _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]
    · rw [GE_eq hi q hq, GQ_eq (kPI_spec hi hj).1 _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]
  rw [h, mul_inv_cancel_right]

@[expose] noncomputable def gpF (i : ℕ) (hi : i < 4) (j : Fin 32) : Fin 32 :=
  ⟨GP i j, (kPI_spec hi j.2).1⟩

theorem gpF_val {i : ℕ} (hi : i < 4) (j : Fin 32) : (gpF i hi j : ℕ) = GP i j := rfl

theorem gpF_bij {i : ℕ} (hi : i < 4) : Function.Bijective (gpF i hi) := by
  refine Finite.injective_iff_bijective.1 fun j j' e => Fin.ext (QP_inj j.2 j'.2 ?_)
  have e' : QP (gpF i hi j) = QP (gpF i hi j') := congrArg (fun x : Fin 32 => QP x) e
  rw [gpF_val, gpF_val, ← EP_conj hi j.2, ← EP_conj hi j'.2] at e'
  exact mul_left_cancel (mul_right_cancel e')

@[expose] noncomputable def sig (i : ℕ) : Equiv.Perm (Fin 32) :=
  if hi : i < 4 then Equiv.ofBijective (gpF i hi) (gpF_bij hi) else 1

theorem sig_apply {i : ℕ} (hi : i < 4) (j : Fin 32) : (sig i j : ℕ) = GP i j := by
  rw [sig, dif_pos hi, Equiv.ofBijective_apply, gpF_val]

theorem EP_mem_normalizer {i : ℕ} (hi : i < 4) :
    EP i ∈ normalizer (Q0 : Set (Equiv.Perm (Fin 820))) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [EP_conj hi hj]
    exact QP_mem_Q0 (kPI_spec hi hj).1
  · rintro ⟨y, hy, hy'⟩
    obtain ⟨j, hj⟩ := (gpF_bij hi).2 ⟨y, hy⟩
    have e : GP i j = y := by rw [← gpF_val hi j, hj]
    rw [← e, ← EP_conj hi j.2] at hy'
    have := mul_left_cancel (mul_right_cancel hy')
    rw [← this]
    exact QP_mem_Q0 j.2

theorem H4_le_normalizer : H4 ≤ normalizer (Q0 : Set (Equiv.Perm (Fin 820))) := by
  rw [H4, closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi : i < 4 := hi
  rw [SetLike.mem_coe, ← EP_eq hi]
  exact EP_mem_normalizer hi

end CertificateChecks.KernelU43CentPlus

end
