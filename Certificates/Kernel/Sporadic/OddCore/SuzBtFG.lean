
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtTG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtFF
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BTupISound
import CFSG.Certificates.Kernel.Spor.BTupOSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Co1.Module.TwoBCert
public import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtFG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG
  CertificateChecks.KernelSpor.SuzBtOG CertificateChecks.KernelSpor.SuzBtTG
  CertificateChecks.KernelSpor.SuzBtFF

theorem kBM21 : allN 4 (fun j => Nat.beq (SuzBtM21.G j) (decK (m21Decs.getD j ([], 0)))) =
    true := by quickRfl

theorem kBK : allN 2 (fun j => Nat.beq (SuzBtK.G j) (decK (l1CompDecs.getD j ([], 0)))) =
    true := by quickRfl

theorem kTau : allN 3 (fun t => Nat.beq (pg 11 (mask 11) (decK tauDec)
    (pg 11 (mask 11) (SuzTwG 6) (pg 11 (mask 11) SuzBtT0.B t)))
    (pg 11 (mask 11) (SuzTwG 6) (pg 11 (mask 11) (decK tauDec) (pg 11 (mask 11) SuzBtT0.B t)))) =
    true := by quickRfl

theorem kTauB : allN 4 (fun i => Bool.not (allN 16 (fun q => Bool.not (allN 3 (fun t =>
    Nat.beq (btWalk 11 (mask 11) SuzBtM21.G SuzBtM21.R q
      (pg 11 (mask 11) (decK tauDec) (pg 11 (mask 11) SuzBtT0.B t)))
      (pg 11 (mask 11) (decK tauDec) (pg 11 (mask 11) (SuzBtL1.G i)
        (pg 11 (mask 11) SuzBtT0.B t)))))))) = true := by quickRfl

theorem not_allN_not_iff {n : Nat} {f : Nat → Bool} :
    Bool.not (allN n (fun q => Bool.not (f q))) = true ↔ ∃ q < n, f q = true := by
  constructor
  · exact exists_of_not_allN_not
  · rintro ⟨q, hq, hf⟩
    cases e : allN n (fun q => Bool.not (f q))
    · rfl
    · have := CFSG.KS.Raw.Orb.allN_iff.1 e q hq
      rw [hf] at this
      exact absurd this Bool.false_ne_true

theorem bIf_true {c a b : Bool} (hc : c = true) : bIf(c, a, b) = a := by
  rw [CFSG.KS.Raw.Orb.bIf_eq, if_pos hc]

theorem bIf_false {c a b : Bool} (hc : c ≠ true) : bIf(c, a, b) = b := by
  rw [CFSG.KS.Raw.Orb.bIf_eq, if_neg hc]

theorem bAnd_iff {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true]

theorem bOr_iff {a b : Bool} : bIf(a, true, b) = true ↔ a = true ∨ b = true := by
  by_cases h : a = true
  · rw [bIf_true h]
    exact ⟨fun _ => Or.inl h, fun _ => rfl⟩
  · rw [bIf_false h]
    exact ⟨Or.inr, fun h' => h'.resolve_left h⟩

theorem not_true_iff {a : Bool} : Bool.not a = true ↔ ¬ a = true := by
  cases a <;> simp

noncomputable abbrev TT : Subgroup (Equiv.Perm (Fin 1782)) := genSub 1782 4 t0Gen

theorem cnt_lt {i : Nat} (hi : i < 64) : i < SuzBtT0.cnt := by
  rw [SuzBtTF.kT0Cnt]
  exact hi

theorem TT_le : TT ≤ invE 1 := fun _ h => T0_le_invE (t0_eq ▸ h)

theorem st_ex {i : Nat} (hi : i < 64) : ∃ h ∈ TT, ∀ t : Fin 3,
    pg 11 (mask 11) (btKey 33 (mask 33) SuzBtT0.K i) t = h (c1Base t) :=
  btKey_mem hgT hbT hpT (cnt_lt hi)

noncomputable def el (i : Nat) : Equiv.Perm (Fin 1782) :=
  if h : i < 64 then Classical.choose (st_ex h) else 1

theorem el_mem {i : Nat} (hi : i < 64) : el i ∈ TT := by
  unfold el
  rw [dif_pos hi]
  exact (Classical.choose_spec (st_ex hi)).1

theorem el_key {i : Nat} (hi : i < 64) (t : Fin 3) :
    pg 11 (mask 11) (btKey 33 (mask 33) SuzBtT0.K i) t = el i (c1Base t) := by
  unfold el
  rw [dif_pos hi]
  exact (Classical.choose_spec (st_ex hi)).2 t

theorem el_of {i : Nat} (hi : i < 64) {x : Equiv.Perm (Fin 1782)} (hx : x ∈ TT)
    (he : ∀ t : Fin 3, pg 11 (mask 11) (btKey 33 (mask 33) SuzBtT0.K i) t = x (c1Base t)) :
    el i = x :=
  ext_of_base hfixT (el_mem hi) hx fun t => Fin.ext (by rw [← el_key hi t, he t])

theorem el_cover {x : Equiv.Perm (Fin 1782)} (hx : x ∈ TT) : ∃ i < 64, el i = x := by
  obtain ⟨i, hi, he⟩ := btKey_cover hgT hbT hpT SuzBtTF.kT0Hd hx
  rw [SuzBtTF.kT0Cnt] at hi
  exact ⟨i, hi, el_of hi hx he⟩

theorem el_inj {i j : Nat} (hi : i < 64) (hj : j < 64) (h : el i = el j) : i = j :=
  btKey_inj (by norm_num) hpT (cnt_lt hi) (cnt_lt hj) fun t => by
    rw [el_key hi t, el_key hj t, h]

theorem el_mul {a q : Nat} (ha : a < 64) (hq : q < 64) :
    mulT a q < 64 ∧ el (mulT a q) = el a * el q := by
  obtain ⟨h1, h2⟩ := btMul_spec hgT hpT hfixT hbT hST hrT (cnt_lt ha) (cnt_lt hq) (el_mem ha)
    (el_key ha) (el_mem hq) (el_key hq)
  rw [SuzBtTF.kT0Cnt] at h1
  exact ⟨h1, el_of h1 (Subgroup.mul_mem _ (el_mem ha) (el_mem hq)) h2⟩

theorem el_pos {i j : Nat} (hi : i < 64) (hj : j < 4) :
    btPos SuzBtT0.POS 4 i j < 64 ∧ el (btPos SuzBtT0.POS 4 i j) = t0Gen j * el i := by
  obtain ⟨h1, h2⟩ := (ptFacts (hpT i (cnt_lt hi))).clos j hj
  rw [SuzBtTF.kT0Cnt] at h1
  refine ⟨h1, el_of h1 (Subgroup.mul_mem _ (gp_mem hj) (el_mem hi)) fun t => ?_⟩
  rw [h2 t t.2, el_key hi t, hgT j hj, Equiv.Perm.mul_apply]

theorem el_rt {i j : Nat} (hi : i < 64) (hj : j < 4) :
    btPos SuzBtT0Z.RT 4 i j < 64 ∧ el (btPos SuzBtT0Z.RT 4 i j) = el i * t0Gen j := by
  obtain ⟨h1, h2⟩ := btRt_spec (y := t0Gen) hgT hpT hfixT hbT hST hrT (cnt_lt hi) (el_mem hi)
    (el_key hi) hj
  rw [SuzBtTF.kT0Cnt] at h1
  exact ⟨h1, el_of h1 (Subgroup.mul_mem _ (el_mem hi) (gp_mem hj)) h2⟩

theorem el_one {i : Nat} (hi : i < 64) : btDep (btRec SuzBtT0.R i) = 0 ↔ el i = 1 :=
  dep0_iff hpT hfixT hbT (by norm_num) SuzBtTF.kT0Hd (cnt_lt hi) (el_mem hi) (el_key hi)

theorem mem_cent_iff {k : Nat} {gp : Nat → Equiv.Perm (Fin 1782)} {x : Equiv.Perm (Fin 1782)} :
    x ∈ Subgroup.centralizer (genSub 1782 k gp : Set (Equiv.Perm (Fin 1782))) ↔
      ∀ j < k, gp j * x = x * gp j := by
  constructor
  · intro h j hj
    exact Subgroup.mem_centralizer_iff.1 h _ (gp_mem hj)
  · intro h
    have hle : genSub 1782 k gp ≤ Subgroup.centralizer {x} := by
      refine Subgroup.closure_le _ |>.2 ?_
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact h j hj
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem czT_iff {i : Nat} (hi : i < 64) :
    czT i = true ↔ el i ∈ Subgroup.centralizer (TT : Set (Equiv.Perm (Fin 1782))) := by
  rw [mem_cent_iff]
  unfold czT
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall₂_congr fun j hj => ?_
  rw [Nat.beq_eq, ← (el_pos hi hj).2, ← (el_rt hi hj).2]
  exact ⟨fun h => by rw [h], fun h => el_inj (el_pos hi hj).1 (el_rt hi hj).1 h⟩

theorem inKT_iff {k cnt base : Nat} {G K R POS : Nat → Nat} {gp : Nat → Equiv.Perm (Fin 1782)}
    (hle : genSub 1782 k gp ≤ invE 1)
    (hg : ∀ j < k, ∀ x : Fin 1782, pg 11 (mask 11) (G j) x = gp j x)
    (hb : ∀ t : Fin 3, pg 11 (mask 11) base t = c1Base t) (hc : btHdK cnt = true)
    (hp : ∀ q < cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) k cnt base G K R POS q = true)
    {i : Nat} (hi : i < 64) : inKT cnt K i = true ↔ el i ∈ genSub 1782 k gp := by
  unfold inKT
  rw [CFSG.KS.Raw.Orb.strictB_eq, not_allN_not_iff]
  constructor
  · rintro ⟨p, hp', he⟩
    exact mem_of_btKey hle hg hb hp hp' (TT_le (el_mem hi)) fun t => by
      rw [← Nat.beq_eq.mp he, el_key hi t]
  · intro hx
    obtain ⟨p, hp', he⟩ := btKey_cover hg hb hp hc hx
    refine ⟨p, hp', Nat.beq_eq.mpr ?_⟩
    exact CFSG.KS.PF.eq_of_fields (by norm_num) (ptFacts (hpT i (cnt_lt hi))).canon
      (ptFacts (hp p hp')).canon fun t ht => by rw [el_key hi ⟨t, ht⟩, he ⟨t, ht⟩]

theorem card_states (P : Equiv.Perm (Fin 1782) → Prop) (f : Nat → Bool)
    (hP : ∀ x, P x → x ∈ TT) (hf : ∀ i < 64, f i = true ↔ P (el i)) :
    Nat.card {x // P x} = btCntN 64 f := by
  rw [btCntN_eq]
  set T := (Finset.range 64).filter (fun i => f i = true)
  have hT : T.card = Nat.card {i : Nat // i ∈ T} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hT]
  have hmemT : ∀ i ∈ T, i < 64 ∧ f i = true := fun i hi => by
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact hi
  let φ : {i : Nat // i ∈ T} → {x // P x} := fun i =>
    ⟨el i.1, (hf i.1 (hmemT i.1 i.2).1).1 (hmemT i.1 i.2).2⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun i j e => Subtype.ext (el_inj (hmemT i.1 i.2).1 (hmemT j.1 j.2).1
      (congrArg Subtype.val e)), fun x => ?_⟩
    obtain ⟨i, hi, he⟩ := el_cover (hP x.1 x.2)
    have hiT : i ∈ T := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, (hf i hi).2 (he ▸ x.2)⟩
    exact ⟨⟨i, hiT⟩, Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective φ hbij)).symm

@[expose] noncomputable def m21gp (j : Nat) : Equiv.Perm (Fin 1782) :=
  decPerm (m21Decs.getD j ([], 0))

@[expose] noncomputable def kgp (j : Nat) : Equiv.Perm (Fin 1782) :=
  decPerm (l1CompDecs.getD j ([], 0))

theorem m21Decs_ok {i : Nat} (hi : i < 4) : (∀ k ∈ (m21Decs.getD i ([], 0)).1, k < 10) ∧
    (m21Decs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem kDecs_ok {i : Nat} (hi : i < 2) : (∀ k ∈ (l1CompDecs.getD i ([], 0)).1, k < 10) ∧
    (l1CompDecs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem hgM21 : ∀ j < 4, ∀ x : Fin 1782, pg 11 (mask 11) (SuzBtM21.G j) x = m21gp j x :=
  fun j hj x => by
    rw [Nat.eq_of_beq_eq_true (allN_spec kBM21 j hj)]
    exact pg_decK (m21Decs_ok hj).1 (m21Decs_ok hj).2 x

theorem hgK : ∀ j < 2, ∀ x : Fin 1782, pg 11 (mask 11) (SuzBtK.G j) x = kgp j x :=
  fun j hj x => by
    rw [Nat.eq_of_beq_eq_true (allN_spec kBK j hj)]
    exact pg_decK (kDecs_ok hj).1 (kDecs_ok hj).2 x

theorem hbM21 : ∀ t : Fin 3, pg 11 (mask 11) SuzBtM21.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem hbK : ∀ t : Fin 3, pg 11 (mask 11) SuzBtK.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem hpM21 : ∀ i < SuzBtM21.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtM21.cnt
    SuzBtM21.B SuzBtM21.G SuzBtM21.K SuzBtM21.R SuzBtM21.POS i = true := fun i hi =>
  btSl_spec SuzBtFF.kM21Sl (Nat.zero_le _) (by rw [SuzBtFF.kM21Cnt] at hi; omega) hi

theorem hpK : ∀ i < SuzBtK.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 2 SuzBtK.cnt
    SuzBtK.B SuzBtK.G SuzBtK.K SuzBtK.R SuzBtK.POS i = true := fun i hi =>
  btSl_spec SuzBtFF.kKSl (Nat.zero_le _) (by rw [SuzBtFF.kKCnt] at hi; omega) hi

theorem m21_eq : genSub 1782 4 m21gp = decSubgroup m21Decs := genSub_dec m21Decs

theorem k_eq : genSub 1782 2 kgp = decSubgroup l1CompDecs := genSub_dec l1CompDecs

theorem m21_le : genSub 1782 4 m21gp ≤ invE 1 := by
  rw [m21_eq]
  exact decSubgroup_le_invE (by decide)

theorem k_le : genSub 1782 2 kgp ≤ invE 1 := by
  rw [k_eq]
  exact decSubgroup_le_invE (by decide)

theorem inLT_iff {i : Nat} (hi : i < 64) : inLT i = true ↔ el i ∈ genSub 1782 4 lgp :=
  inKT_iff l1_le hgL hbL SuzBtZF.kL1Hd hpL hi

theorem inMT_iff {i : Nat} (hi : i < 64) : inMT i = true ↔ el i ∈ genSub 1782 4 m21gp :=
  inKT_iff m21_le hgM21 hbM21 SuzBtFF.kM21Hd hpM21 hi

theorem le_TT {G : Nat → Nat} {gp : Nat → Equiv.Perm (Fin 1782)}
    (hle : genSub 1782 4 gp ≤ invE 1)
    (hg : ∀ j < 4, ∀ x : Fin 1782, pg 11 (mask 11) (G j) x = gp j x)
    (h : allN 4 (fun j => Bool.not (allN 64 (fun q => Bool.not (btMov 11 (mask 11) 3
      (G j) SuzBtT0.B (btKey 33 (mask 33) SuzBtT0.K q))))) = true) :
    genSub 1782 4 gp ≤ TT := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨q, hq, hm⟩ := exists_of_not_allN_not (CFSG.KS.Raw.Orb.allN_iff.1 h j hj)
  exact mem_of_btKey TT_le hgT hbT hpT (cnt_lt hq) (hle (gp_mem hj)) (mov_base hbT (hg j hj) hm)

theorem l1_le_TT : genSub 1782 4 lgp ≤ TT := le_TT l1_le hgL SuzBtFF.kLT

theorem m21_le_TT : genSub 1782 4 m21gp ≤ TT := le_TT m21_le hgM21 SuzBtFF.kMT

noncomputable abbrev ZZ : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.centralizer (TT : Set (Equiv.Perm (Fin 1782))) ⊓ TT

theorem mem_ZZ_iff {i : Nat} (hi : i < 64) : el i ∈ ZZ ↔ czT i = true := by
  rw [Subgroup.mem_inf, czT_iff hi]
  exact ⟨fun h => h.1, fun h => ⟨h, el_mem hi⟩⟩

theorem card_ZZ : Nat.card ZZ = 4 := by
  have h := card_states (fun x => x ∈ ZZ) czT (fun _ h => (Subgroup.mem_inf.1 h).2)
    fun i hi => (mem_ZZ_iff hi).symm
  rw [Nat.beq_eq.mp SuzBtFF.kZ] at h
  exact h

theorem inf_eq : genSub 1782 4 lgp ⊓ genSub 1782 4 m21gp = ZZ := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hl, hm⟩
    obtain ⟨i, hi, rfl⟩ := el_cover (l1_le_TT hl)
    have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtFF.kLM i hi
    by_cases hc : czT i = true
    · exact (mem_ZZ_iff hi).2 hc
    · rw [bIf_false hc, not_true_iff, bAnd_iff, inLT_iff hi, inMT_iff hi] at h
      exact absurd ⟨hl, hm⟩ h
  · intro hz
    obtain ⟨i, hi, rfl⟩ := el_cover (Subgroup.mem_inf.1 hz).2
    have hc := (mem_ZZ_iff hi).1 hz
    have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtFF.kLM i hi
    rw [bIf_true hc, bAnd_iff, inLT_iff hi, inMT_iff hi] at h
    exact h

theorem inv_mem {x : Equiv.Perm (Fin 1782)} (hx : x ∈ TT) (h2 : x * x = 1) (h1 : x ≠ 1) :
    x ∈ genSub 1782 4 lgp ∨ x ∈ genSub 1782 4 m21gp := by
  obtain ⟨i, hi, rfl⟩ := el_cover hx
  have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtFF.kInv i hi
  have hm := el_mul hi hi
  have hc : bAnd(Bool.not (Nat.beq (btDep (btRec SuzBtT0.R i)) 0),
      Nat.beq (btDep (btRec SuzBtT0.R (mulT i i))) 0) = true := by
    rw [bAnd_iff, not_true_iff, Nat.beq_eq, Nat.beq_eq, el_one hi, el_one hm.1, hm.2]
    exact ⟨h1, h2⟩
  rw [bIf_true hc, bOr_iff, inLT_iff hi, inMT_iff hi] at h
  exact h

theorem not_mem_ZZ {i : Nat} (hi : i < 64) (h : el i ∉ ZZ) : czT i ≠ true :=
  fun hc => h ((mem_ZZ_iff hi).2 hc)

theorem noncomm {x y : Equiv.Perm (Fin 1782)} (hx : x ∈ genSub 1782 4 lgp) (hxz : x ∉ ZZ)
    (hy : y ∈ genSub 1782 4 m21gp) (hyz : y ∉ ZZ) : x * y ≠ y * x := by
  obtain ⟨i, hi, rfl⟩ := el_cover (l1_le_TT hx)
  obtain ⟨j, hj, rfl⟩ := el_cover (m21_le_TT hy)
  have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtFF.kNC i hi
  rw [bIf_true (bAnd_iff.2 ⟨(inLT_iff hi).2 hx, not_true_iff.2 (not_mem_ZZ hi hxz)⟩)] at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
  rw [bIf_true (bAnd_iff.2 ⟨(inMT_iff hj).2 hy, not_true_iff.2 (not_mem_ZZ hj hyz)⟩),
    not_true_iff, Nat.beq_eq] at h'
  intro e
  apply h'
  rw [← (el_mul hi hj).2, ← (el_mul hj hi).2] at e
  exact el_inj (el_mul hi hj).1 (el_mul hj hi).1 e

theorem card_cent {x : Equiv.Perm (Fin 1782)}
    (hx : x ∈ genSub 1782 4 lgp ∨ x ∈ genSub 1782 4 m21gp) (hxz : x ∉ ZZ) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ TT) = 16 := by
  have hxT : x ∈ TT := hx.elim (fun h => l1_le_TT h) (fun h => m21_le_TT h)
  obtain ⟨i, hi, rfl⟩ := el_cover hxT
  have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtFF.kCen i hi
  have hn : ncT i = true := by
    unfold ncT
    rw [bAnd_iff, bOr_iff, inLT_iff hi, inMT_iff hi, not_true_iff]
    exact ⟨hx, not_mem_ZZ hi hxz⟩
  rw [bIf_true hn, Nat.beq_eq] at h
  rw [← h]
  refine card_states (fun y => y ∈ Subgroup.centralizer ({el i} : Set _) ⊓ TT) _
    (fun _ h => (Subgroup.mem_inf.1 h).2) fun j hj => ?_
  rw [Nat.beq_eq, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro e
    refine ⟨?_, el_mem hj⟩
    rw [← (el_mul hi hj).2, ← (el_mul hj hi).2, e]
  · rintro ⟨e, -⟩
    refine el_inj (el_mul hi hj).1 (el_mul hj hi).1 ?_
    rw [(el_mul hi hj).2, (el_mul hj hi).2, e]

theorem card_K : Nat.card (genSub 1782 2 kgp) = 4 := by
  rw [card_genSub_of_btK (by norm_num) k_le hgK hbK SuzBtFF.kKHd hpK, SuzBtFF.kKCnt]

theorem k_inf_l1 : genSub 1782 2 kgp ⊓ genSub 1782 4 lgp = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hk, hl⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  obtain ⟨s, hs, he⟩ := btKey_cover hgK hbK hpK SuzBtFF.kKHd hk
  have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtFF.kKL s hs
  by_cases h0 : Nat.beq (btDep (btRec SuzBtK.R s)) 0 = true
  · refine invE1_eq_one (k_le hk) fun t => Fin.ext ?_
    rw [← he t, (ptFacts (hpK s hs)).root (Nat.beq_eq.mp h0), hbK t]
  · rw [bIf_false h0] at h
    obtain ⟨p, hp, hpe⟩ := btKey_cover hgL hbL hpL SuzBtZF.kL1Hd hl
    have h' := CFSG.KS.Raw.Orb.allN_iff.1 h p hp
    rw [not_true_iff, Nat.beq_eq] at h'
    exact absurd (CFSG.KS.PF.eq_of_fields (by norm_num) (ptFacts (hpK s hs)).canon
      (ptFacts (hpL p hp)).canon fun t ht => by rw [he ⟨t, ht⟩, hpe ⟨t, ht⟩]) h'

theorem V0_conj {g : Equiv.Perm (Fin 1782)} (hg : g ∈ V0) {h : Equiv.Perm (Fin 1782)}
    (hh : h ∈ T0) : g * h * g⁻¹ ∈ T0 := by
  have hgM : g ∈ suzM := invE_le_suzM (mem_V0_iff.1 hg).2
  rw [T0_eq_closure_twoA] at hh ⊢
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxV, c, hc, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxV)
      (Subgroup.inv_mem _ hg), g * c, Subgroup.mul_mem _ hgM hc, by group⟩
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem V0_le_norm : V0 ≤ Subgroup.normalizer (T0 : Set (Equiv.Perm (Fin 1782))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact V0_conj hg
  · intro hh
    have e : h = g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ := by group
    rw [e]
    exact V0_conj (Subgroup.inv_mem _ hg) hh

theorem tauDec_ok : (∀ k ∈ tauDec.1, k < 10) ∧ tauDec.2 < 128 := by decide

theorem tau_mem : decPerm tauDec ∈ invE 1 := decPerm_mem tauDec_ok.1

theorem hTau : ∀ x : Fin 1782, pg 11 (mask 11) (decK tauDec) x = decPerm tauDec x :=
  pg_decK tauDec_ok.1 tauDec_ok.2

theorem tau_V0 : decPerm tauDec ∈ V0 := by
  refine mem_V0_iff.2 ⟨invE1_ext (Subgroup.mul_mem _ tau_mem w_mem)
    (Subgroup.mul_mem _ w_mem tau_mem) fun t => Fin.ext ?_, tau_mem⟩
  have h := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 kTau t t.2)
  rw [hbT t, hW, hTau, hTau, hW] at h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact h

theorem hfixM21 : ∀ h ∈ genSub 1782 4 m21gp, (∀ t, h (c1Base t) = c1Base t) → h = 1 :=
  fun h hh hf => invE1_eq_one (m21_le hh) hf

theorem tau_conj {i : Nat} (hi : i < 4) :
    decPerm tauDec * lgp i * (decPerm tauDec)⁻¹ ∈ genSub 1782 4 m21gp := by
  obtain ⟨q, hq, he⟩ := exists_of_not_allN_not (CFSG.KS.Raw.Orb.allN_iff.1 kTauB i hi)
  have hq' : q < SuzBtM21.cnt := by
    rw [SuzBtFF.kM21Cnt]
    exact hq
  obtain ⟨m, hm, hme⟩ := btKey_mem hgM21 hbM21 hpM21 hq'
  have e : m * decPerm tauDec = decPerm tauDec * lgp i := by
    refine invE1_ext (Subgroup.mul_mem _ (m21_le hm) tau_mem)
      (Subgroup.mul_mem _ tau_mem (l1_le (gp_mem hi))) fun t => Fin.ext ?_
    have h := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 he t t.2)
    rw [hbT t, hTau, hgL i hi, hTau,
      btWalk_spec hgM21 hpM21 hfixM21 hbM21 hq' hm hme] at h
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact h
  rw [← e, mul_inv_cancel_right]
  exact hm

theorem sq_mem {x : Equiv.Perm (Fin 1782)} (hx : x ∈ TT) : x * x ∈ ZZ := by
  obtain ⟨i, hi, rfl⟩ := el_cover hx
  have hm := el_mul hi hi
  rw [← hm.2, mem_ZZ_iff hm.1]
  exact CFSG.KS.Raw.Orb.allN_iff.1 SuzBtFF.kSq i hi

theorem comm_of_sq {x y : Equiv.Perm (Fin 1782)} (hx : x ∈ TT) (hy : y ∈ TT) :
    x * y * x⁻¹ * y⁻¹ ∈ ZZ := by
  have ha := sq_mem hx
  have hb := sq_mem hy
  have hc := sq_mem (Subgroup.mul_mem _ hx hy)
  have hay : Commute (x * x) y :=
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ha).1 y hy).symm
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = x * y * x * ((x * x)⁻¹ * y) * (y * y)⁻¹ := by group
      _ = x * y * x * (y * (x * x)⁻¹) * (y * y)⁻¹ := by rw [hay.inv_left.eq]
      _ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem f5Prop : F5Prop := by
  unfold F5Prop
  dsimp only
  rw [tabSubgroup_t0Tabs, tabSubgroup_v0Tabs, ← l1_eq, ← m21_eq, ← k_eq, ← t0_eq]
  have hb : ∀ i : Fin 4, l1BasisPerm i.val = lgp i := fun i => by
    have hi : (i : Nat) < l1Decs.length := by
      rw [show l1Decs.length = 4 from rfl]
      exact i.2
    unfold l1BasisPerm lgp
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
  refine ⟨card_ZZ, l1_le_TT, m21_le_TT, Subgroup.le_normalizer, inf_eq,
    fun x hx h2 h1 => inv_mem hx h2 h1, fun x hx hxz y hy hyz => noncomm hx hxz hy hyz,
    fun x hx hxz => card_cent (Or.inl hx) hxz, fun y hy hyz => card_cent (Or.inr hy) hyz,
    card_K, k_inf_l1, ?_, tau_V0, fun i => ?_, fun x hx => sq_mem hx,
    fun x hx y hy => comm_of_sq hx hy⟩
  · rw [t0_eq]
    exact V0_le_norm
  · rw [hb i]
    exact tau_conj i.2

end CertificateChecks.KernelSpor.SuzBtFG

end
