module

public import Certificates.Kernel.Sporadic.Fi24G2e.Own
public import Certificates.Kernel.Sporadic.Fi24Orb.Simple
public import Certificates.Kernel.Sporadic.Fi24Ext.Final
public import CFSG.Sporadic.Fi24.OctadAction
import Mathlib.Tactic.Group

public section

namespace CertificateChecks.KernelFi24G2g

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix CertificateChecks.KernelFi24Orb
  CertificateChecks.KernelFi24Ext CertificateChecks.KernelFi24G2e TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KC.Fi24FixK CFSG.KC.Fi24FixS CFSG.KC.Fi24FixC

open CFSG.Sporadic.Fi24 (R J jR tR tT cls pt)
open CFSG.KD.Fi24Orb (NM NI)
open CFSG.KD.Fi24G2e (OQ2 OQ4 OQ6)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction

@[expose] def PtRank : Prop :=
  ∀ k < 306936, (CFSG.Sporadic.Fi24.pt k).sp = f k


theorem J_eq_Γ : J = Γ := by
  rw [← Jc_eq]
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)

theorem mT_eq : CFSG.Sporadic.Fi24.mT = Mt CFSG.KD.Fi24Ext.T :=
  CFSG.Sporadic.Fi24.matW_matT.symm.trans T_facts.2

theorem τ_mem_R (q : Fi24AutomorphismGroup) : τ q ∈ R := by
  have h := τ_mem_closure tT (by rw [CFSG.Sporadic.Fi24.coe_tT, mT_eq]) q
  rw [← J_eq_Γ] at h
  exact h

@[expose] noncomputable def ρ : Fi24AutomorphismGroup →* R := τ.codRestrict R τ_mem_R

theorem coe_ρ (q : Fi24AutomorphismGroup) : ((ρ q : R) : GL (Fin 781) (ZMod 3)) = τ q := rfl

theorem ρ_eq_iff {q p : Fi24AutomorphismGroup} : ρ q = ρ p ↔ τ q = τ p :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem pt_smul_R (x : R) (k : Fin 306936) :
    (pt (x • k).val).sp = act (x : GL (Fin 781) (ZMod 3)) (pt k.val).sp := by
  have hJ : ∀ (g : J) (k : Fin 306936),
      (pt (jR g • k).val).sp = act ((jR g : R) : GL (Fin 781) (ZMod 3)) (pt k.val).sp := by
    intro g k
    rw [CFSG.Sporadic.Fi24.jR_smul, CFSG.Sporadic.Fi24.pt_smul, CFSG.Sporadic.Fi24.smul_sp]
    rfl
  have hT : ∀ k : Fin 306936,
      (pt (tR • k).val).sp = act ((tR : R) : GL (Fin 781) (ZMod 3)) (pt k.val).sp := by
    intro k
    rw [CFSG.Sporadic.Fi24.tR_smul, CFSG.Sporadic.Fi24.pt_tPerm, CFSG.Sporadic.Fi24.tSub_sp]
    rfl
  obtain ⟨g, rfl | rfl⟩ := CFSG.Sporadic.Fi24.eq_jR_or x
  · exact hJ g k
  · rw [mul_smul, hJ, hT, Subgroup.coe_mul, act_mul]

@[expose] noncomputable def pk {r : ℕ} (hr : r < 306936) : Fin 306936 := ⟨NI r, NI_lt hr⟩

theorem f_pk {r : ℕ} (hr : r < 306936) : f (pk hr) = ψ r := by
  rw [f_def]
  change ψ (NM (NI r)) = ψ r
  rw [NM_NI hr]

theorem pk_inj {r r' : ℕ} (hr : r < 306936) (hr' : r' < 306936) (h : pk hr = pk hr') : r = r' := by
  have e : NI r = NI r' := congrArg Fin.val h
  rw [← NM_NI hr, ← NM_NI hr', e]

theorem pk_NM (k : Fin 306936) : pk (NM_lt k.isLt) = k := Fin.ext (NI_NM k.isLt)

theorem pk_congr {r r' : ℕ} (hr : r < 306936) (hr' : r' < 306936) (h : r = r') : pk hr = pk hr' := by
  subst h
  rfl

theorem eq_of_f {k k' : Fin 306936} (h : f k = f k') : k = k' :=
  Fin.ext (f_inj k.isLt k'.isLt h)

theorem cls_comm_iff (k l : Fin 306936) : cls k * cls l = cls l * cls k ↔ cls k • l = l := by
  constructor
  · intro h
    apply CFSG.Sporadic.Fi24.cls_injective
    rw [CFSG.Sporadic.Fi24.cls_smul_R, h, mul_inv_cancel_right]
  · intro h
    have e := CFSG.Sporadic.Fi24.cls_smul_R (cls k) l
    rw [h] at e
    calc cls k * cls l = cls k * cls l * (cls k)⁻¹ * cls k := by group
      _ = cls l * cls k := by rw [← e]

theorem uP_J : uP ∈ J := by rw [J_eq_Γ]; exact uP_mem

@[expose] def plW : List (ℕ × Bool) → List ℕ
  | [] => []
  | l :: t => plW t ++ (if l.2 then [l.1 + 1, 0] else [0, l.1 + 1])

theorem plW_cons (l : ℕ × Bool) (t : List (ℕ × Bool)) :
    plW (l :: t) = plW t ++ (if l.2 then [l.1 + 1, 0] else [0, l.1 + 1]) := rfl

theorem plW_lt : ∀ t : List (ℕ × Bool), (∀ l ∈ t, l.1 < 11) → ∀ g ∈ plW t, g < 12
  | [], _, g, hg => absurd hg List.not_mem_nil
  | l :: t, ht, g, hg => by
    rw [plW_cons] at hg
    rcases List.mem_append.1 hg with h | h
    · exact plW_lt t (fun l' h' => ht l' (List.mem_cons_of_mem l h')) g h
    · have := ht l List.mem_cons_self
      split at h <;> simp at h <;> omega

theorem τ_pair {k : ℕ} (hk : k < 11) : τ (g0 0 * g0 (k + 1)) = xs k := by
  rw [map_mul, τ_g0_zero, τ_g0_succ hk, ← mul_assoc, uT_mul_uT, one_mul]

theorem act_x {k : ℕ} (hk : k < 11) {s : ℕ} (hs : s < 306936) :
    act (xs k) (ψ s) = ψ (walk CFSG.KD.Fi24Fix.TG [k + 1, 0] s) := by
  rw [ψ_walk_τ (by intro g hg; simp at hg; omega) hs]
  have e : (([k + 1, 0] : List ℕ).map g0).prod⁻¹ = g0 0 * g0 (k + 1) := by
    simp [g0_inv]
  rw [← map_inv, e, τ_pair hk]

theorem act_wordProd_ψ : ∀ (t : List (ℕ × Bool)), (∀ l ∈ t, l.1 < 11) → ∀ {r : ℕ},
    r < 306936 → act (wordProd xs t) (ψ r) = ψ (walk CFSG.KD.Fi24Fix.TG (plW t) r)
  | [], _, r, _ => by rw [wordProd, List.map_nil, List.prod_nil, act_one]; rfl
  | l :: t, ht, r, hr => by
    have hl := ht l List.mem_cons_self
    have ht' : ∀ l' ∈ t, l'.1 < 11 := fun l' h => ht l' (List.mem_cons_of_mem l h)
    have hw := plW_lt t ht'
    have e : wordProd xs (l :: t) =
        (if l.2 then xs l.1 else (xs l.1)⁻¹) * wordProd xs t := by
      simp only [wordProd, List.map_cons, List.prod_cons]
    rw [e, act_mul, act_wordProd_ψ t ht' hr, plW_cons, walk_append]
    have hr' := walk_lt hw hr
    split
    · exact act_x hl hr'
    · rw [← ψ_tk hl hr', tk_eq]

theorem NM_zero : CFSG.KD.Fi24Orb.NM 0 = 62038 := by decide +kernel

theorem plW_walk : walk CFSG.KD.Fi24Fix.TG (plW pl) 62038 = 37886 := by decide +kernel

theorem act_uP : act uP (ψ 62038) = ψ 37886 := by
  rw [uP, act_wordProd_ψ pl pl_lt (by norm_num), plW_walk]

section Bind

variable (hP : PtRank)
include hP

theorem f_smul (x : R) (k : Fin 306936) :
    f (x • k).val = act (x : GL (Fin 781) (ZMod 3)) (f k) := by
  rw [← hP _ (x • k).isLt, ← hP _ k.isLt, pt_smul_R]

theorem smul_pk {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {r : ℕ} (hr : r < 306936) :
    (ρ (wp w))⁻¹ • pk hr = pk (walk_lt hw hr) := by
  apply eq_of_f
  rw [f_smul hP, f_pk, f_pk, ψ_walk_τ hw hr, Subgroup.coe_inv, coe_ρ]

theorem smul_pk_letter {g : ℕ} (hg : g < 12) {r : ℕ} (hr : r < 306936) :
    ρ (g0 g) • pk hr = pk (walk_lt (w := [g]) (by simpa using hg) hr) := by
  have h := smul_pk hP (w := [g]) (by simpa using hg) hr
  have e : (wp [g])⁻¹ = g0 g := by simp [wp, g0_inv]
  rwa [← map_inv, e] at h

theorem uP_smul_root :
    (⟨uP, uP_J⟩ : J) • CFSG.Sporadic.Fi24.root = pk (r := 37886) (by norm_num) := by
  apply eq_of_f
  have h := f_smul hP (jR ⟨uP, uP_J⟩) CFSG.Sporadic.Fi24.root
  rw [CFSG.Sporadic.Fi24.jR_smul] at h
  rw [h, f_pk, CFSG.Sporadic.Fi24.coe_jR]
  change act uP (f 0) = _
  rw [f_def, NM_zero, act_uP]

theorem cls_own0 : cls (pk (r := 37886) (by norm_num)) = ρ (g0 0) := by
  rw [← uP_smul_root hP, CFSG.Sporadic.Fi24.cls_smul_root]
  apply Subtype.ext
  rw [coe_ρ, τ_g0_zero, uT_eq tT (by rw [CFSG.Sporadic.Fi24.coe_tT, mT_eq])]
  rfl

theorem cls_pk_walk {q : List ℕ} (hq : ∀ g ∈ q, g < 12) :
    cls (pk (walk_lt hq (r := 37886) (by norm_num))) = ρ ((wp q)⁻¹ * g0 0 * wp q) := by
  rw [← smul_pk hP hq (r := 37886) (by norm_num), CFSG.Sporadic.Fi24.cls_smul_R, cls_own0 hP, map_mul, map_mul, map_inv,
    inv_inv]

theorem cls_pk_walk' {q : List ℕ} (hq : ∀ g ∈ q, g < 12) {x : ℕ} (hx : x < 306936)
    (h : walk CFSG.KD.Fi24Fix.TG q 37886 = x) :
    cls (pk hx) = ρ ((wp q)⁻¹ * g0 0 * wp q) := by
  rw [← cls_pk_walk hP hq, pk_congr _ _ h]

theorem cls_own :
    cls (pk (r := 37886) (by norm_num)) = ρ (g0 0) ∧ cls (pk (r := 22978) (by norm_num)) = ρ (g0 2) ∧
    cls (pk (r := 22975) (by norm_num)) = ρ (g0 4) ∧ cls (pk (r := 22973) (by norm_num)) = ρ (g0 6) := by
  obtain ⟨w2, w4, w6, t2, t4, t6⟩ := letter_own
  have e : ∀ (q : List ℕ) (g : ℕ), τ (g0 g) = (τ (wp q))⁻¹ * uT * τ (wp q) →
      ρ (g0 g) = ρ ((wp q)⁻¹ * g0 0 * wp q) := fun q g h => by
    rw [ρ_eq_iff, h, map_mul, map_mul, map_inv, τ_g0_zero]
  have l2 : ∀ g ∈ OQ2, g < 12 := fun g hg => oq_lt g (by simp [hg])
  have l4 : ∀ g ∈ OQ4, g < 12 := fun g hg => oq_lt g (by simp [hg])
  have l6 : ∀ g ∈ OQ6, g < 12 := fun g hg => oq_lt g (by simp [hg])
  exact ⟨cls_own0 hP, (cls_pk_walk' hP l2 _ w2).trans (e _ _ t2).symm,
    (cls_pk_walk' hP l4 _ w4).trans (e _ _ t4).symm, (cls_pk_walk' hP l6 _ w6).trans (e _ _ t6).symm⟩

end Bind

end CertificateChecks.KernelFi24G2g

end
