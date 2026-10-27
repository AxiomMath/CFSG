module

public import Certificates.Kernel.L34Tw.Checks
public import Certificates.Kernel.LocalComp.L34Para.Final
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRAFacts
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Tw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KC.L34KSnd CFSG.KC.L34Scan CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts
open CertificateChecks.KernelLC.L34Cert CertificateChecks.KernelLC.L34Para
open CFSG.KC.L34Tw CertificateChecks.KernelLC.L34TwD
open CFSG.KLie.CT (andB orB notB)

@[expose] def Rp (x : Nat) (g : Equiv.Perm (Fin 42)) : Prop :=
  canonK 42 6 (mask 6) (42 * 6) x = true ∧ TabRep (unpack 42 6 x) g

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem Rp.mul {x y : Nat} {g h : Equiv.Perm (Fin 42)} (hx : Rp x g) (hy : Rp y h) :
    Rp (mulK x y) (g * h) := by
  refine ⟨canonK_pcomp hx.1 hy.1, ?_⟩
  unfold mulK
  rw [← comp_unpack' hx.1 hy.1]
  exact hx.2.comp hy.2

theorem Rp.beq_iff {x y : Nat} {g h : Equiv.Perm (Fin 42)} (hx : Rp x g) (hy : Rp y h) :
    Nat.beq x y = true ↔ g = h := by
  constructor
  · intro e
    rw [Nat.eq_of_beq_eq_true e] at hx
    exact hx.2.perm_eq hy.2
  · rintro rfl
    rw [unpack_inj' hx.1 hy.1 (hx.2.tab_eq hy.2)]
    exact Nat.beq_refl y

theorem rp_id : Rp CFSG.KC.L34Tw.idK 1 := by
  refine ⟨canon_pidn hsz42, ?_⟩
  unfold CFSG.KC.L34Tw.idK
  rw [← idTab_unpack' hsz42]
  exact TabRep.idTab

theorem Rp.inv2 {x : Nat} {g : Equiv.Perm (Fin 42)} (hx : Rp x g) :
    inv2K x = true ↔ g * g = 1 :=
  (hx.mul hx).beq_iff rp_id

theorem Rp.comm {x y : Nat} {g h : Equiv.Perm (Fin 42)} (hx : Rp x g) (hy : Rp y h) :
    CFSG.KC.L34Tw.commK x y = true ↔ g * h = h * g :=
  (hx.mul hy).beq_iff (hy.mul hx)

theorem rp₅ : Rp (L34R.G 4) g₅ := ⟨cnG (by decide), e5 ▸ tabRep_g₅⟩

theorem rp₆ : Rp (L34R.G 5) g₆ := ⟨cnG (by decide), e6 ▸ tabRep_g₆⟩

theorem enumT : Enumerates T0 (pts 42 6 64 L34PT.T).toList := by
  have h := enumerates_wordClosure rT.2.1
  rw [rT.1] at h
  exact h

theorem rpT {q : Nat} (hq : q < 64) : ∃ g ∈ T0, Rp (L34PT.T q) g := by
  have hm : (pts 42 6 64 L34PT.T)[q]! ∈ (pts 42 6 64 L34PT.T).toList := by
    rw [getElem!_pos _ q (by rw [size_pts]; exact hq)]
    exact Array.getElem_mem_toList _
  obtain ⟨g, hg, hr⟩ := enumT.sound _ hm
  rw [pts_get' hq] at hr
  exact ⟨g, hg, rT.2.2.1 q hq, hr⟩

theorem rpT' {g : Equiv.Perm (Fin 42)} (hg : g ∈ T0) : ∃ q < 64, Rp (L34PT.T q) g := by
  obtain ⟨t, ht, hr⟩ := enumT.complete g hg
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  rw [size_pts] at hi
  rw [pts_get' hi] at hr
  exact ⟨i, hi, rT.2.2.1 i hi, hr⟩

theorem Rp.mem_T0 {x : Nat} {g : Equiv.Perm (Fin 42)} (hx : Rp x g) (h : memT L34PT.T x = true) :
    g ∈ T0 := by
  obtain ⟨q, hq, e⟩ := memK_spec (N := 64) h
  obtain ⟨g', hg', hr⟩ := rpT hq
  rw [e] at hr
  rwa [hx.2.perm_eq hr.2]

theorem rpG {i : Nat} (hi : i < 4) : Rp (L34PT.G i) (wordPerm (wT₀.getD i [])) := by
  have hl : i < wT₀.length := hi
  obtain ⟨e, c⟩ := rT.2.2.2.2 i hi
  refine ⟨c, ?_⟩
  rw [← e, List.getD_eq_getElem _ _ hl]
  exact tabRep_wordTabs wT₀ hl

theorem norm_ok : inv2K (L34R.G 4) = true ∧ inv2K (L34R.G 5) = true ∧
    CFSG.KC.L34Tw.commK (L34R.G 4) (L34R.G 5) = true ∧ ∀ i < 4,
      memT L34PT.T (mulK (mulK (L34R.G 4) (L34PT.G i)) (L34R.G 4)) = true ∧
      memT L34PT.T (mulK (mulK (L34R.G 5) (L34PT.G i)) (L34R.G 5)) = true := by
  have h := ch33101_norm
  unfold CFSG.KC.L34Tw.normK at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  exact ⟨h1, h2, h3, fun i hi => andB_iff.1 (allN' h i hi)⟩

theorem g₅_sq : g₅ * g₅ = 1 := rp₅.inv2.1 norm_ok.1

theorem g₆_sq : g₆ * g₆ = 1 := rp₆.inv2.1 norm_ok.2.1

theorem g₅g₆_comm : g₅ * g₆ = g₆ * g₅ := (rp₅.comm rp₆).1 norm_ok.2.2.1

theorem conj_mem_of {h : Equiv.Perm (Fin 42)} (hh : h * h = 1)
    (hg : ∀ i < 4, h * wordPerm (wT₀.getD i []) * h ∈ T0) {x : Equiv.Perm (Fin 42)}
    (hx : x ∈ T0) : h * x * h ∈ T0 := by
  have hinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  have hle : T0 ≤ T0.comap (MulAut.conj h).toMonoidHom := by
    unfold T0
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hi4 : i < 4 := hi
    have := hg i hi4
    rw [List.getD_eq_getElem _ _ hi] at this
    change h * _ * h⁻¹ ∈ T0
    rwa [hinv]
  have := hle hx
  change h * x * h⁻¹ ∈ T0 at this
  rwa [hinv] at this

theorem conj_g₅_mem {x : Equiv.Perm (Fin 42)} (hx : x ∈ T0) : g₅ * x * g₅ ∈ T0 :=
  conj_mem_of g₅_sq (fun i hi => ((rp₅.mul (rpG hi)).mul rp₅).mem_T0 (norm_ok.2.2.2 i hi).1) hx

theorem conj_g₆_mem {x : Equiv.Perm (Fin 42)} (hx : x ∈ T0) : g₆ * x * g₆ ∈ T0 :=
  conj_mem_of g₆_sq (fun i hi => ((rp₆.mul (rpG hi)).mul rp₆).mem_T0 (norm_ok.2.2.2 i hi).2) hx

theorem idx_facts : ∀ q < 64, Nat.blt q 64 = true ∧ Nat.land q 63 = q ∧
    Nat.blt (64 + q) 64 = false ∧ Nat.land (64 + q) 63 = q := by
  decide

theorem klein_of_rec {x : Nat} {s : Equiv.Perm (Fin 42)} (hx : Rp x s) {r : Nat}
    (h : kleinK L34PT.T x r = true) : ∃ e₁ e₂, e₁ ∈ T0 ∧ e₂ ∈ T0 ∧ e₁ * e₁ = 1 ∧
      e₂ * e₂ = 1 ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₂ ≠ e₁ ∧ e₁ * e₂ = e₂ * e₁ ∧ e₁ * s = s * e₁ ∧
      e₂ * s = s * e₂ := by
  unfold kleinK at h
  obtain ⟨hr, h⟩ := andB_iff.1 h
  rw [sB, sB] at h
  have hr' : r < 4096 := Nat.le_of_ble_eq_true hr
  have ha : Nat.land r 63 < 64 := Nat.and_lt_two_pow (n := 6) r (by decide)
  have hb : Nat.shiftRight r 6 < 64 := by
    change r >>> 6 < 64
    rw [Nat.shiftRight_eq_div_pow]
    omega
  obtain ⟨e₁, m₁, r₁⟩ := rpT ha
  obtain ⟨e₂, m₂, r₂⟩ := rpT hb
  obtain ⟨i₁, h⟩ := andB_iff.1 h
  obtain ⟨i₂, h⟩ := andB_iff.1 h
  obtain ⟨n₁, h⟩ := andB_iff.1 h
  obtain ⟨n₂, h⟩ := andB_iff.1 h
  obtain ⟨n₁₂, h⟩ := andB_iff.1 h
  obtain ⟨c₁₂, h⟩ := andB_iff.1 h
  obtain ⟨c₁, c₂⟩ := andB_iff.1 h
  refine ⟨e₁, e₂, m₁, m₂, r₁.inv2.1 i₁, r₂.inv2.1 i₂, ?_, ?_, ?_, (r₁.comm r₂).1 c₁₂,
    (r₁.comm hx).1 c₁, (r₂.comm hx).1 c₂⟩
  · intro e
    rw [notB_iff] at n₁
    rw [(r₁.beq_iff rp_id).2 e] at n₁
    exact absurd n₁ (by decide)
  · intro e
    rw [notB_iff] at n₂
    rw [(r₂.beq_iff rp_id).2 e] at n₂
    exact absurd n₂ (by decide)
  · intro e
    rw [notB_iff] at n₁₂
    rw [(r₁.beq_iff r₂).2 e.symm] at n₁₂
    exact absurd n₁₂ (by decide)

theorem klein_of_inv {h t : Equiv.Perm (Fin 42)} (hh : h = g₅ ∨ h = g₆) (ht : t ∈ T0)
    (hs : h * t * (h * t) = 1) : ∃ e₁ e₂, e₁ ∈ T0 ∧ e₂ ∈ T0 ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧
      e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₂ ≠ e₁ ∧ e₁ * e₂ = e₂ * e₁ ∧ e₁ * (h * t) = h * t * e₁ ∧
      e₂ * (h * t) = h * t * e₂ := by
  obtain ⟨q, hq, rq⟩ := rpT' ht
  obtain ⟨b₁, l₁, b₂, l₂⟩ := idx_facts q hq
  have hk := allN' ch33201_klein
  rcases hh with rfl | rfl
  · have h' := hk q (by omega)
    simp only [b₁, l₁, sB] at h'
    have hx := rp₅.mul rq
    rw [orB_iff, notB_iff, hx.inv2.2 hs] at h'
    exact klein_of_rec hx (h'.resolve_left (by decide))
  · have h' := hk (64 + q) (by omega)
    simp only [b₂, l₂, sB] at h'
    have hx := rp₆.mul rq
    rw [orB_iff, notB_iff, hx.inv2.2 hs] at h'
    exact klein_of_rec hx (h'.resolve_left (by decide))

theorem exists_t : ∃ u ∈ T0, g₅ * u * (g₅ * u) = 1 ∧ g₅ * (g₅ * u) = g₅ * u * g₅ ∧
    g₅ * g₆ * (g₅ * u) = g₅ * u * (g₅ * g₆) ∧ g₅ * u ≠ g₅ := by
  have h := ch33209_t
  unfold tK at h
  obtain ⟨hq, h⟩ := andB_iff.1 h
  rw [sB] at h
  obtain ⟨u, hu, ru⟩ := rpT (Nat.le_of_ble_eq_true hq)
  have hx := rp₅.mul ru
  obtain ⟨i, h⟩ := andB_iff.1 h
  obtain ⟨c₅, h⟩ := andB_iff.1 h
  obtain ⟨c₅₆, n⟩ := andB_iff.1 h
  refine ⟨u, hu, hx.inv2.1 i, (rp₅.comm hx).1 c₅, ((rp₅.mul rp₆).comm hx).1 c₅₆, fun e => ?_⟩
  rw [notB_iff, (hx.beq_iff rp₅).2 e] at n
  exact absurd n (by decide)

open CFSG.ComponentClassification.GrSLit.L34Tw in
theorem raHyp : RAHyp :=
  ⟨g₅_sq, g₆_sq, g₅g₆_comm, fun _ hx => conj_g₅_mem hx, fun _ hx => conj_g₆_mem hx⟩

section Facts

open CFSG.ComponentClassification.GrSLit.L34Tw


theorem facts33101 : Nat.card RA = 256 ∧ RA ⊓ S = T0 := ⟨raHyp.card_eq, raHyp.inf_S_eq⟩

theorem facts33102 : ∀ x ∈ RA, ∀ y ∈ RA, (cosRA (x * y)).val = (cosRA x).val ^^^ (cosRA y).val :=
  fun _ hx _ hy => raHyp.cos_mul hx hy

theorem facts33201 : ∀ s ∈ RA, s * s = 1 → (cosRA s = 1 ∨ cosRA s = 2) → ∃ e₁ e₂, e₁ ∈ T0 ∧
    e₂ ∈ T0 ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₂ ≠ e₁ ∧ e₁ * e₂ = e₂ * e₁ ∧
    e₁ * s = s * e₁ ∧ e₂ * s = s * e₂ :=
  raHyp.klein_inv fun _ _ hk ht hs => klein_of_inv hk ht hs

theorem facts33209 : ∃ t ∈ RA, cosRA t = 1 ∧ t * t = 1 ∧ g₅ * t = t * g₅ ∧
    g₅ * g₆ * t = t * (g₅ * g₆) ∧ g₅ * g₆ = g₆ * g₅ ∧ t ≠ g₅ :=
  raHyp.exists_t5 exists_t

end Facts

end CertificateChecks.KernelLC.L34Tw

end
