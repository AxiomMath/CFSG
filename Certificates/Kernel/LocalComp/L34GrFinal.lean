module

public import Certificates.Kernel.LocalComp.L34GrChk
public import Certificates.Kernel.LocalComp.L34GrS0
public import Certificates.Kernel.LocalComp.L34GrS1
public import Certificates.Kernel.LocalComp.L34N3Final
public import Certificates.Kernel.LocalComp.L34Bo.Final
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelLC.L34Gr.grSlAll CertificateChecks.KernelLC.L34Gr.grSl 18

namespace CertificateChecks.KernelLC.L34Gr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.KC.L34Scan CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.L34Borel
open CFSG.KLie.CT (andB orB notB anyN)

theorem orB_not {a b : Bool} (h : orB (notB a) b = true) (ha : a = true) : b = true := by
  rcases CFSG.KC.L34KSnd.orB_iff.1 h with h | h
  · rw [CFSG.KC.L34KSnd.notB_iff, ha] at h
    exact Bool.noConfusion h
  · exact h

theorem exists_of_notB_allN {n : ℕ} {f : ℕ → Bool} (h : notB (allN n f) = true) :
    ∃ i < n, f i = false := by
  by_contra hc
  push Not at hc
  have hall : allN n f = true := CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => by
    cases e : f i
    · exact absurd e (hc i hi)
    · rfl
  rw [CFSG.KC.L34KSnd.notB_iff, hall] at h
  exact Bool.noConfusion h

theorem beqP {p q : ℕ} {a b : Equiv.Perm (Fin 42)} (hp : canonK 42 6 (mask 6) (42 * 6) p = true)
    (hq : canonK 42 6 (mask 6) (42 * 6) q = true) (ha : TabRep (unpack 42 6 p) a)
    (hb : TabRep (unpack 42 6 q) b) : Nat.beq p q = true ↔ a = b := by
  constructor
  · intro h
    rw [Nat.eq_of_beq_eq_true h] at ha
    exact ha.perm_eq hb
  · intro e
    rw [CFSG.KC.L34KSnd.unpack_inj' hp hq ((ha.eq_iff hb).2 e)]
    exact Nat.beq_refl q

theorem commP {p q : ℕ} {a b : Equiv.Perm (Fin 42)} (hp : canonK 42 6 (mask 6) (42 * 6) p = true)
    (hq : canonK 42 6 (mask 6) (42 * 6) q = true) (ha : TabRep (unpack 42 6 p) a)
    (hb : TabRep (unpack 42 6 q) b) : commPt 42 6 p q = true ↔ a * b = b * a := by
  rw [CFSG.KC.L34KSnd.commPt_iff hp hq]
  exact (ha.comp hb).eq_iff (hb.comp ha)

theorem sqP {p : ℕ} {a : Equiv.Perm (Fin 42)} (hp : canonK 42 6 (mask 6) (42 * 6) p = true)
    (ha : TabRep (unpack 42 6 p) a) :
    canonK 42 6 (mask 6) (42 * 6) (sq p) = true ∧ TabRep (unpack 42 6 (sq p)) (a * a) := by
  unfold sq
  rw [← CFSG.KC.L34KSnd.comp_unpack' hp hp]
  exact ⟨canonK_pcomp hp hp, ha.comp ha⟩

theorem idP : canonK 42 6 (mask 6) (42 * 6) (pidn 42 6) = true ∧
    TabRep (unpack 42 6 (pidn 42 6)) (1 : Equiv.Perm (Fin 42)) := by
  rw [← CFSG.KC.L34KSnd.idTab_unpack' hsz42]
  exact ⟨CFSG.KC.L34KSnd.canon_pidn hsz42, TabRep.idTab⟩

theorem S_rep {q : ℕ} (hq : q < 20160) :
    ∃ g ∈ S, TabRep (unpack 42 6 (L34S.T q)) g := by
  refine enumerates_S.sound _ ?_
  have e : (enumBFS 42 gensS 20160).tabs[q]! = unpack 42 6 (L34S.T q) := by
    rw [hS.1]
    exact CFSG.KC.L34KSnd.pts_get hq
  rw [← e]
  exact getElem!_mem (by rw [hS.1, size_pts]; exact hq)

theorem exists_S {x : Equiv.Perm (Fin 42)} (hx : x ∈ S) :
    ∃ k < 20160, TabRep (unpack 42 6 (L34S.T k)) x := by
  obtain ⟨k, hk, h⟩ := enumerates_S.exists_pos hx
  have hk' : k < 20160 := by
    rw [hS.1, size_pts] at hk
    exact hk
  have e : (enumBFS 42 gensS 20160).tabs[k]! = unpack 42 6 (L34S.T k) := by
    rw [hS.1]
    exact CFSG.KC.L34KSnd.pts_get hk'
  rw [e] at h
  exact ⟨k, hk', h⟩

theorem J_lt {q : ℕ} (hq : q < 7755) : L34N.J q / 32 < 241920 := by
  obtain ⟨k, -, hk, -, h32, hJ⟩ := L34N.listed.get q (Nat.zero_le _) hq
  omega

theorem topF : L34Bo.inS X0 = true ∧ L34Bo.fa 0 = 1 ∧ L34Bo.fb 0 = 27 ∧
    ∀ p < 42, p = 1 ∨ p = 27 ∨ ∃ i < 4, Nat.beq (pg 6 (mask 6) (L34Bo.syG 0 i) p) p = false := by
  have h := kTop
  unfold top at h
  obtain ⟨h1, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h2, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h3, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  refine ⟨h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, fun p hp => ?_⟩
  have hq := CFSG.KS.Raw.Orb.allN_iff.1 h p hp
  beta_reduce at hq
  rcases CFSG.KC.L34KSnd.orB_iff.1 hq with e | hq
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  rcases CFSG.KC.L34KSnd.orB_iff.1 hq with e | hq
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true e))
  · exact Or.inr (Or.inr (exists_of_notB_allN hq))

theorem x0_rep : canonK 42 6 (mask 6) (42 * 6) X0 = true ∧
    ∃ x₀ ∈ S, TabRep (unpack 42 6 X0) x₀ := by
  obtain ⟨q, hq, e⟩ := L34Bo.inS_iff.1 topF.1
  rw [← e]
  exact ⟨pinS.canon q hq, S_rep hq⟩

noncomputable def T0 : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure {a | ∃ i < 4, TabRep (unpack 42 6 (L34Bo.syG 0 i)) a}

theorem gen_rep {i : ℕ} (hi : i < 4) :
    ∃ a ∈ S, TabRep (unpack 42 6 (L34Bo.syG 0 i)) a := by
  obtain ⟨q, hq, e⟩ := L34Bo.inS_iff.1 ((L34Bo.syl_all 0 (by decide)).gens.2 i hi).2.2
  rw [← e]
  exact S_rep hq

theorem enum_T0 : Enumerates T0 (sylEnum 0).tabs.toList := by
  have F := L34Bo.syl_all 0 (by decide)
  refine enumerates_closure (gens := sylGens[0]!) (fun a ha => ?_) (fun j hj => ?_) F.ok
  · obtain ⟨i, hi, h⟩ := ha
    exact ⟨i, by rw [F.gens.1]; exact hi, by rw [(F.gens.2 i hi).1]; exact h⟩
  · rw [F.gens.1] at hj
    obtain ⟨a, -, h⟩ := gen_rep hj
    exact ⟨a, ⟨j, hj, h⟩, by rw [(F.gens.2 j hj).1]; exact h⟩

theorem T0_le_S : T0 ≤ S := by
  unfold T0
  rw [Subgroup.closure_le]
  rintro a ⟨i, hi, ha⟩
  obtain ⟨b, hbS, hb⟩ := gen_rep hi
  rw [ha.perm_eq hb]
  exact hbS

theorem card_T0 : Nat.card T0 = 64 := by
  rw [enum_T0.card, Array.length_toList]
  exact (L34Bo.syl_all 0 (by decide)).size

theorem fix_T0 {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) :
    (t ⟨1, by decide⟩ : ℕ) = 1 ∧ (t ⟨27, by decide⟩ : ℕ) = 27 := by
  have F := L34Bo.syl_all 0 (by decide)
  obtain ⟨k, hk, h⟩ := enum_T0.exists_pos ht
  rw [F.size] at hk
  rw [F.get k hk] at h
  have hf := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 L34Bo.k_fix 0 (by decide)) k hk
  beta_reduce at hf
  obtain ⟨h1, h2⟩ := CFSG.KC.L34KSnd.andB_iff.1 hf
  rw [topF.2.1] at h1
  rw [topF.2.2.1] at h2
  have e1 : (unpack 42 6 (L34Bo.syT 0 k))[1]! = (t ⟨1, by decide⟩ : ℕ) := h.apply ⟨1, by decide⟩
  have e27 : (unpack 42 6 (L34Bo.syT 0 k))[27]! = (t ⟨27, by decide⟩ : ℕ) :=
    h.apply ⟨27, by decide⟩
  rw [CFSG.KC.BfsPin.unpack_get' (n := 42) (p := 1) (by decide)] at e1
  rw [CFSG.KC.BfsPin.unpack_get' (n := 42) (p := 27) (by decide)] at e27
  exact ⟨e1.symm.trans (Nat.eq_of_beq_eq_true h1), e27.symm.trans (Nat.eq_of_beq_eq_true h2)⟩

theorem fixed_pt {p : Fin 42} (h : ∀ t ∈ T0, t p = p) :
    (p : ℕ) = 1 ∨ (p : ℕ) = 27 := by
  rcases topF.2.2.2 p p.isLt with e | e | ⟨i, hi, hb⟩
  · exact Or.inl e
  · exact Or.inr e
  · exfalso
    obtain ⟨a, -, ha⟩ := gen_rep hi
    have haT : a ∈ T0 := Subgroup.subset_closure ⟨i, hi, ha⟩
    have e := ha.apply p
    rw [CFSG.KC.BfsPin.unpack_get' p.isLt, h a haT] at e
    rw [e, Nat.beq_refl] at hb
    exact Bool.noConfusion hb

def PairSt (y : Equiv.Perm (Fin 42)) : Prop :=
  ((y ⟨1, by decide⟩ : ℕ) = 1 ∨ (y ⟨1, by decide⟩ : ℕ) = 27) ∧
    ((y ⟨27, by decide⟩ : ℕ) = 1 ∨ (y ⟨27, by decide⟩ : ℕ) = 27)

theorem PairSt.apply {y : Equiv.Perm (Fin 42)} (h : PairSt y) {i : Fin 42}
    (hi : (i : ℕ) = 1 ∨ (i : ℕ) = 27) : (y i : ℕ) = 1 ∨ (y i : ℕ) = 27 := by
  rcases hi with hi | hi
  · have e : i = ⟨1, by decide⟩ := Fin.ext hi
    rw [e]
    exact h.1
  · have e : i = ⟨27, by decide⟩ := Fin.ext hi
    rw [e]
    exact h.2

theorem PairSt.mul {a b : Equiv.Perm (Fin 42)} (ha : PairSt a) (hb : PairSt b) : PairSt (a * b) :=
  ⟨ha.apply (hb.apply (Or.inl rfl)), ha.apply (hb.apply (Or.inr rfl))⟩

theorem PairSt.inv {y : Equiv.Perm (Fin 42)} (h : PairSt y) : PairSt y⁻¹ := by
  have key : ∀ i : Fin 42, ((i : ℕ) = 1 ∨ (i : ℕ) = 27) →
      ((y⁻¹ i : ℕ) = 1 ∨ (y⁻¹ i : ℕ) = 27) := by
    intro i hi
    have hne : (y ⟨1, by decide⟩ : ℕ) ≠ (y ⟨27, by decide⟩ : ℕ) := fun e =>
      absurd (congrArg Fin.val (y.injective (Fin.ext e))) (by decide)
    obtain ⟨h1, h27⟩ := h
    have hc : i = y ⟨1, by decide⟩ ∨ i = y ⟨27, by decide⟩ := by
      rcases hi with hi | hi <;> rcases h1 with h1 | h1 <;> rcases h27 with h27 | h27 <;>
        first
        | exact absurd (h1.trans h27.symm) hne
        | exact Or.inl (Fin.ext (hi.trans h1.symm))
        | exact Or.inr (Fin.ext (hi.trans h27.symm))
    have e1 : y⁻¹ (y ⟨1, by decide⟩) = ⟨1, by decide⟩ := by simp
    have e27 : y⁻¹ (y ⟨27, by decide⟩) = ⟨27, by decide⟩ := by simp
    rcases hc with rfl | rfl
    · rw [e1]
      exact Or.inl rfl
    · rw [e27]
      exact Or.inr rfl
  exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩

theorem PairSt_of_norm {y : Equiv.Perm (Fin 42)}
    (hy : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0) : PairSt y := by
  have key : ∀ p : Fin 42, ((p : ℕ) = 1 ∨ (p : ℕ) = 27) →
      ((y⁻¹ p : ℕ) = 1 ∨ (y⁻¹ p : ℕ) = 27) := by
    intro p hp
    refine fixed_pt fun t ht => ?_
    have hfix : (y * t * y⁻¹) p = p := by
      obtain ⟨f1, f27⟩ := fix_T0 (hy t ht)
      rcases hp with hp | hp
      · have e : p = ⟨1, by decide⟩ := Fin.ext hp
        rw [e]
        exact Fin.ext f1
      · have e : p = ⟨27, by decide⟩ := Fin.ext hp
        rw [e]
        exact Fin.ext f27
    calc t (y⁻¹ p) = y⁻¹ ((y * t * y⁻¹) p) := by
          simp [Equiv.Perm.mul_apply]
      _ = y⁻¹ p := by rw [hfix]
  have h : PairSt y⁻¹ := ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩
  have h' := h.inv
  rwa [inv_inv] at h'

theorem listed_of_PairSt {y : Equiv.Perm (Fin 42)} (hy : y ∈ R)
    (h : PairSt y) : ∃ q < 7755, L34N.J q / 4 % 2 = 1 ∧ L34N.J q / 32 < 241920 ∧
      TabRep (unpack 42 6 (L34R.T (L34N.J q / 32))) y := by
  obtain ⟨i, hi, hrep⟩ := L34N3.exists_T hy
  have a1 : (unpack 42 6 (L34R.T i))[1]! = (y ⟨1, by decide⟩ : ℕ) := hrep.apply ⟨1, by decide⟩
  have a27 : (unpack 42 6 (L34R.T i))[27]! = (y ⟨27, by decide⟩ : ℕ) :=
    hrep.apply ⟨27, by decide⟩
  obtain ⟨q, hq, hqi, hb⟩ := (L34N.stabT_iff hi).1 (by
    unfold PairSt at h
    rw [a1, a27]
    exact h)
  refine ⟨q, hq, hb, by rw [hqi]; exact hi, by rw [hqi]; exact hrep⟩

theorem PairSt_of_listed {q : ℕ} (hq : q < 7755) (hb : L34N.J q / 4 % 2 = 1)
    {y : Equiv.Perm (Fin 42)} (hrep : TabRep (unpack 42 6 (L34R.T (L34N.J q / 32))) y) :
    PairSt y := by
  have h := (L34N.stabT_iff (J_lt hq)).2 ⟨q, hq, rfl, hb⟩
  have a1 : (unpack 42 6 (L34R.T (L34N.J q / 32)))[1]! = (y ⟨1, by decide⟩ : ℕ) :=
    hrep.apply ⟨1, by decide⟩
  have a27 : (unpack 42 6 (L34R.T (L34N.J q / 32)))[27]! = (y ⟨27, by decide⟩ : ℕ) :=
    hrep.apply ⟨27, by decide⟩
  rw [a1, a27] at h
  exact h

theorem inY_of {q : ℕ} {x₀ ρ : Equiv.Perm (Fin 42)} (cX0 : canonK 42 6 (mask 6) (42 * 6) X0 = true)
    (hx₀ : TabRep (unpack 42 6 X0) x₀) (hb : L34N.J q / 4 % 2 = 1) (hi : L34N.J q / 32 < 241920)
    (hrep : TabRep (unpack 42 6 (L34R.T (L34N.J q / 32))) ρ) (hρx : ρ * x₀ = x₀ * ρ) :
    inY X0 (L34N.J q) = true := by
  unfold inY
  rw [CFSG.KC.L34KSnd.andB_iff]
  exact ⟨Nat.beq_eq.mpr hb, (commP (L34N.canonT hi) cX0 hrep hx₀).2 hρx⟩

theorem Y_facts {x₀ : Equiv.Perm (Fin 42)}
    (cX0 : canonK 42 6 (mask 6) (42 * 6) X0 = true) (hx₀ : TabRep (unpack 42 6 X0) x₀)
    {ρ : Equiv.Perm (Fin 42)} (hρR : ρ ∈ R) (hρS : PairSt ρ) (hρx : ρ * x₀ = x₀ * ρ) :
    (ρ ^ 4 = 1 → ρ ^ 2 = 1) ∧
    (ρ ^ 2 = 1 → ρ ≠ 1 →
      (∀ ρ' ∈ R, PairSt ρ' → ρ' * x₀ = x₀ * ρ' → ρ' ^ 2 = 1 → ρ' ≠ 1 → ρ * ρ' = ρ' * ρ →
        ρ = ρ') ∧
      (∀ τ ∈ S, τ * x₀ = x₀ * τ → τ * ρ = ρ * τ → τ = 1 ∨ τ = x₀ ∨ τ = x₀ * x₀)) := by
  obtain ⟨cE, hE⟩ := idP
  obtain ⟨q, hq, hb, hi, hrep⟩ := listed_of_PairSt hρR hρS
  have cr := L34N.canonT hi
  have hY := kY
  unfold grY at hY
  have hYq := CFSG.KS.Raw.Orb.allN_iff.1 hY q hq
  beta_reduce at hYq
  rw [CFSG.KC.L34Norm.strictB_eq] at hYq
  beta_reduce at hYq
  rw [inY_of cX0 hx₀ hb hi hrep hρx] at hYq
  have hP : yPt (pidn 42 6) X0 (L34R.T (L34N.J q / 32)) = true := hYq
  unfold yPt at hP
  obtain ⟨hA, hBC⟩ := CFSG.KC.L34KSnd.andB_iff.1 hP
  obtain ⟨cs, hs⟩ := sqP cr hrep
  obtain ⟨css, hss⟩ := sqP cs hs
  have e2 : ρ ^ 2 = ρ * ρ := pow_two ρ
  have e4 : ρ ^ 4 = ρ * ρ * (ρ * ρ) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  refine ⟨fun h4 => ?_, fun h2 h1 => ?_⟩
  · rw [e2]
    exact (beqP cs cE hs hE).1 (orB_not hA ((beqP css cE hss hE).2 (by rw [← e4]; exact h4)))
  have hBC' := orB_not hBC ((beqP cs cE hs hE).2 (by rw [← e2]; exact h2))
  rcases CFSG.KC.L34KSnd.orB_iff.1 hBC' with h | h
  · exact absurd ((beqP cr cE hrep hE).1 h) h1
  obtain ⟨hB, hC⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  refine ⟨fun ρ' hρ'R hρ'S hρ'x h2' h1' hc => ?_, fun τ hτS hτx hτρ => ?_⟩
  · obtain ⟨q', hq', hb', hi', hrep'⟩ := listed_of_PairSt hρ'R hρ'S
    have cr' := L34N.canonT hi'
    obtain ⟨cs', hs'⟩ := sqP cr' hrep'
    have hBq := CFSG.KS.Raw.Orb.allN_iff.1 hB q' hq'
    beta_reduce at hBq
    rw [CFSG.KC.L34Norm.strictB_eq] at hBq
    beta_reduce at hBq
    rw [inY_of cX0 hx₀ hb' hi' hrep' hρ'x] at hBq
    have hBq' : strictB (L34R.T (L34N.J q' / 32)) (fun r' =>
        orB (notB (Nat.beq (sq r') (pidn 42 6))) (orB (Nat.beq r' (pidn 42 6))
          (orB (notB (commPt 42 6 (L34R.T (L34N.J q / 32)) r'))
            (Nat.beq (L34R.T (L34N.J q / 32)) r')))) = true := hBq
    rw [CFSG.KC.L34Norm.strictB_eq] at hBq'
    beta_reduce at hBq'
    have h3 := orB_not hBq' ((beqP cs' cE hs' hE).2 (by rw [← pow_two]; exact h2'))
    rcases CFSG.KC.L34KSnd.orB_iff.1 h3 with h | h
    · exact absurd ((beqP cr' cE hrep' hE).1 h) h1'
    exact (beqP cr cr' hrep hrep').1 (orB_not h ((commP cr cr' hrep hrep').2 hc))
  · obtain ⟨k, hk, hτrep⟩ := exists_S hτS
    have ct := pinS.canon k hk
    have hCk := CFSG.KS.Raw.Orb.allN_iff.1 hC k hk
    beta_reduce at hCk
    rw [CFSG.KC.L34Norm.strictB_eq] at hCk
    beta_reduce at hCk
    have h3 := orB_not hCk (CFSG.KC.L34KSnd.andB_iff.2
      ⟨(commP ct cX0 hτrep hx₀).2 hτx, (commP ct cr hτrep hrep).2 hτρ⟩)
    obtain ⟨csx, hsx⟩ := sqP cX0 hx₀
    rcases CFSG.KC.L34KSnd.orB_iff.1 h3 with h | h
    · exact Or.inl ((beqP ct cE hτrep hE).1 h)
    rcases CFSG.KC.L34KSnd.orB_iff.1 h with h | h
    · exact Or.inr (Or.inl ((beqP ct cX0 hτrep hx₀).1 h))
    · exact Or.inr (Or.inr ((beqP ct csx hτrep hsx).1 h))

theorem grS_at {k : ℕ} (hk : k < 20160) : grS (pidn 42 6) X0 (L34S.T k) = true :=
  scanSl_spec (L := 1120) (K := 18) (by decide) (by decide) (fun s hs => by
    have h1 := grSlAll s hs
    unfold grSl at h1
    rwa [CFSG.KC.L34Scan.strictB_app] at h1) k hk

theorem conj_x0 {x₀ : Equiv.Perm (Fin 42)}
    (cX0 : canonK 42 6 (mask 6) (42 * 6) X0 = true) (hx₀ : TabRep (unpack 42 6 X0) x₀)
    {x : Equiv.Perm (Fin 42)} (hxS : x ∈ S) (hxN : ∀ t ∈ T0, x * t * x⁻¹ ∈ T0) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : ∃ g ∈ R, PairSt g ∧ x = g * x₀ * g⁻¹ := by
  obtain ⟨k, hk, hxrep⟩ := exists_S hxS
  have ck := pinS.canon k hk
  have hg := grS_at hk
  unfold grS at hg
  rcases CFSG.KC.L34KSnd.orB_iff.1 hg with h | h
  · exfalso
    have hx := PairSt_of_norm hxN
    unfold PairSt at hx
    have a1 : (unpack 42 6 (L34S.T k))[1]! = (x ⟨1, by decide⟩ : ℕ) := hxrep.apply ⟨1, by decide⟩
    have a27 : (unpack 42 6 (L34S.T k))[27]! = (x ⟨27, by decide⟩ : ℕ) :=
      hxrep.apply ⟨27, by decide⟩
    have hp : pairPt 6 1 27 (L34S.T k) = true := by
      rw [pairPt_iff (n := 42) (by decide) (by decide), a1, a27]
      exact hx
    rw [CFSG.KC.L34KSnd.notB_iff, hp] at h
    exact Bool.noConfusion h
  rcases CFSG.KC.L34KSnd.orB_iff.1 h with h | h
  · exfalso
    have ho : o3Pt 42 6 (pidn 42 6) (L34S.T k) = true := (o3Pt_iff ck).2
      ⟨fun e => hx1 ((hxrep.eq_iff TabRep.idTab).1 e),
        ((hxrep.comp (hxrep.comp hxrep)).eq_iff TabRep.idTab).2 (by rw [← pow_three]; exact hx3)⟩
    rw [CFSG.KC.L34KSnd.notB_iff, ho] at h
    exact Bool.noConfusion h
  obtain ⟨q, hq, h⟩ := CFSG.KC.L34Norm.anyN_iff.1 h
  rw [CFSG.KC.L34Norm.strictB_eq] at h
  beta_reduce at h
  obtain ⟨hb, hc⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  have hi := J_lt hq
  have hb' : L34N.J q / 4 % 2 = 1 := Nat.eq_of_beq_eq_true hb
  have hc' : conjPt 42 6 (L34R.T (L34N.J q / 32)) X0 (L34S.T k) = true := hc
  obtain ⟨g, hgR, hgrep⟩ := enumerates_R.sound _ (L34N3.T_mem hi)
  have e := (conjPt_iff (L34N.canonT hi) cX0 ck).1 hc'
  have e' : g * x₀ = x * g := ((hgrep.comp hx₀).eq_iff (hxrep.comp hgrep)).1 e
  exact ⟨g, hgR, PairSt_of_listed hq hb' hgrep, (mul_inv_eq_of_eq_mul e').symm⟩

theorem conj_comm {g a b : Equiv.Perm (Fin 42)} (h : a * (g * b * g⁻¹) = g * b * g⁻¹ * a) :
    g⁻¹ * a * g * b = b * (g⁻¹ * a * g) :=
  calc g⁻¹ * a * g * b = g⁻¹ * (a * (g * b * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * b * g⁻¹ * a) * g := by rw [h]
    _ = b * (g⁻¹ * a * g) := by group

theorem spec :
    ∃ T₀ : Subgroup (Equiv.Perm (Fin 42)), T₀ ≤ S ∧ Nat.card T₀ = 64 ∧
      ∀ x ∈ S, (∀ t ∈ T₀, x * t * x⁻¹ ∈ T₀) → x ^ 3 = 1 → x ≠ 1 →
        (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r → r ^ 4 = 1 → r ^ 2 = 1) ∧
        (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r →
          ∀ r' ∈ R, (∀ t ∈ T₀, r' * t * r'⁻¹ ∈ T₀) → r' * x = x * r' →
            r ^ 2 = 1 → r' ^ 2 = 1 → r ≠ 1 → r' ≠ 1 → r ≠ r' → r * r' ≠ r' * r) ∧
        (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r → r ^ 2 = 1 → r ≠ 1 →
          ∀ t ∈ S, t * x = x * t → t * r = r * t → t = 1 ∨ t = x ∨ t = x * x) := by
  obtain ⟨cX0, x₀, -, hx₀⟩ := x0_rep
  refine ⟨T0, T0_le_S, card_T0, fun x hxS hxN hx3 hx1 => ?_⟩
  obtain ⟨g, hgR, hgS, rfl⟩ := conj_x0 cX0 hx₀ hxS hxN hx3 hx1
  let κ : Equiv.Perm (Fin 42) →* Equiv.Perm (Fin 42) := (MulAut.conj g⁻¹).toMonoidHom
  have hκ : ∀ y, κ y = g⁻¹ * y * g⁻¹⁻¹ := fun y => by simp [κ, MulAut.conj_apply]
  have hκ' : ∀ y, κ y = g⁻¹ * y * g := fun y => by rw [hκ, inv_inv]
  have hκinj : Function.Injective κ := (MulAut.conj g⁻¹).injective
  have hκ1 : ∀ y, κ y = 1 → y = 1 := fun y hy => hκinj (by rw [hy, map_one])
  have hκx : κ (g * x₀ * g⁻¹) = x₀ := by rw [hκ']; group
  have hκR : ∀ y ∈ R, κ y ∈ R := fun y hy => by
    rw [hκ']
    exact R.mul_mem (R.mul_mem (R.inv_mem hgR) hy) hgR
  have hκSt : ∀ r, (∀ t ∈ T0, r * t * r⁻¹ ∈ T0) → PairSt (κ r) := fun r hr => by
    rw [hκ']
    exact (hgS.inv.mul (PairSt_of_norm hr)).mul hgS
  have hκc : ∀ r, r * (g * x₀ * g⁻¹) = g * x₀ * g⁻¹ * r → κ r * x₀ = x₀ * κ r := fun r hr => by
    rw [hκ']
    exact conj_comm hr
  refine ⟨fun r hrR hrN hrx hr4 => ?_, fun r hrR hrN hrx r' hr'R hr'N hr'x hr2 hr'2 hr1 hr'1 hne
    hcomm => ?_, fun r hrR hrN hrx hr2 hr1 t htS htx htr => ?_⟩
  · have h := (Y_facts cX0 hx₀ (hκR r hrR) (hκSt r hrN) (hκc r hrx)).1
      (by rw [← map_pow, hr4, map_one])
    exact hκ1 _ (by rw [map_pow, h])
  · have h := ((Y_facts cX0 hx₀ (hκR r hrR) (hκSt r hrN) (hκc r hrx)).2
      (by rw [← map_pow, hr2, map_one]) (fun h => hr1 (hκ1 r h))).1 (κ r') (hκR r' hr'R)
      (hκSt r' hr'N) (hκc r' hr'x) (by rw [← map_pow, hr'2, map_one]) (fun h => hr'1 (hκ1 r' h))
      (by rw [← map_mul, ← map_mul, hcomm])
    exact hne (hκinj h)
  · have htS' : κ t ∈ S := by
      rw [hκ]
      exact conj_mem_S (R.inv_mem hgR) htS
    have h := ((Y_facts cX0 hx₀ (hκR r hrR) (hκSt r hrN) (hκc r hrx)).2
      (by rw [← map_pow, hr2, map_one]) (fun h => hr1 (hκ1 r h))).2 (κ t) htS' (hκc t htx)
      (by rw [← map_mul, ← map_mul, htr])
    rcases h with h | h | h
    · exact Or.inl (hκ1 t h)
    · exact Or.inr (Or.inl (hκinj (by rw [h, hκx])))
    · exact Or.inr (Or.inr (hκinj (by rw [h, map_mul, hκx])))

end CertificateChecks.KernelLC.L34Gr

end
