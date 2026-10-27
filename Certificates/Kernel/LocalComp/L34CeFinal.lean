module

public import Certificates.Kernel.LocalComp.L34CeChk
public import Certificates.Kernel.LocalComp.L34N3Final
public import Certificates.Kernel.LocalComp.L34Bo.Final
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Ce

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four
open CFSG.KLie.CT (andB orB notB anyN)

theorem ce_pair_form {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) {x : G} (hx : x ∈ Subgroup.closure {a, b}) :
    ∃ k < 9, x = a ^ (k / 3) * b ^ (k % 3) := by
  have hc : Commute a b := hab
  have hm : ∀ {c : G}, c ^ 3 = 1 → ∀ i : ℕ, c ^ i = c ^ (i % 3) := fun hc3 i => by
    conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hc3, one_pow, mul_one]
  suffices h : ∃ i j : ℕ, x = a ^ i * b ^ j by
    obtain ⟨i, j, rfl⟩ := h
    refine ⟨3 * (i % 3) + j % 3, by omega, ?_⟩
    have e1 : (3 * (i % 3) + j % 3) / 3 = i % 3 := by omega
    have e2 : (3 * (i % 3) + j % 3) % 3 = j % 3 := by omega
    rw [e1, e2, ← hm ha, ← hm hb]
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨i', j', rfl⟩ := hy
    refine ⟨i + i', j + j', ?_⟩
    have : b ^ j * a ^ i' = a ^ i' * b ^ j := ((hc.symm.pow_pow j i')).eq
    calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by group
      _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [this]
      _ = a ^ (i + i') * b ^ (j + j') := by rw [pow_add, pow_add]; group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨2 * i, 2 * j, ?_⟩
    have h1 : a ^ i * a ^ (2 * i) = 1 := by
      rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, ha, one_pow]
    have h2 : b ^ j * b ^ (2 * j) = 1 := by
      rw [← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hb, one_pow]
    have hcom : b ^ j * a ^ (2 * i) = a ^ (2 * i) * b ^ j := ((hc.symm.pow_pow j (2 * i))).eq
    rw [inv_eq_iff_mul_eq_one]
    calc a ^ i * b ^ j * (a ^ (2 * i) * b ^ (2 * j))
        = a ^ i * (b ^ j * a ^ (2 * i)) * b ^ (2 * j) := by group
      _ = a ^ i * (a ^ (2 * i) * b ^ j) * b ^ (2 * j) := by rw [hcom]
      _ = (a ^ i * a ^ (2 * i)) * (b ^ j * b ^ (2 * j)) := by group
      _ = 1 := by rw [h1, h2, one_mul]

theorem small : powTab 42 a₀T 3 = idTab 42 ∧ powTab 42 b₀T 3 = idTab 42 ∧
    comp 42 a₀T b₀T = comp 42 b₀T a₀T ∧
    (∀ i < 9, ∀ j < 9, (e9T ())[i]! = (e9T ())[j]! → i = j) ∧
    comp 42 (r₄T ()) (r₄T ()) = idTab 42 ∧ r₄T () ≠ idTab 42 ∧
    comp 42 (r₄T ()) a₀T = comp 42 a₀T (r₄T ()) ∧ comp 42 (r₄T ()) b₀T = comp 42 b₀T (r₄T ()) := by
  decide +kernel

theorem S_mem {q : ℕ} (hq : q < 20160) : unpack 42 6 (L34S.T q) ∈ enumS.tabs.toList := by
  have e : (enumBFS 42 gensS 20160).tabs[q]! = unpack 42 6 (L34S.T q) := by
    rw [hS.1]
    exact CFSG.KC.L34KSnd.pts_get hq
  rw [← e]
  exact getElem!_mem (by rw [hS.1, size_pts]; exact hq)

theorem ce_at {q : ℕ} (hq : q < 7755) (h1 : L34N.J q % 2 = 1) :
    cePt (RP 3) (L34R.T (L34N.J q / 32)) = true := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kCe q hq
  beta_reduce at h
  rw [CFSG.KC.L34Norm.strictB_eq] at h
  beta_reduce at h
  have hb : Nat.beq (Nat.mod (L34N.J q) 2) 1 = true := Nat.beq_eq.mpr h1
  rw [hb] at h
  exact h

theorem canonRP : canonK 42 6 (mask 6) (42 * 6) (RP 3) = true := cnRP (by decide)

theorem commPt_r4 {i : ℕ} (hi : i < 241920) :
    commPt 42 6 (L34R.T i) (RP 3) = true ↔
      comp 42 (unpack 42 6 (L34R.T i)) (r₄T ()) = comp 42 (r₄T ()) (unpack 42 6 (L34R.T i)) := by
  rw [CFSG.KC.L34KSnd.commPt_iff (L34N.canonT hi) canonRP, ← r4_eq]

theorem spec :
    ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ S ∧ Nat.card A₀ = 9 ∧
      ∃ β ∈ R, β ^ 2 = 1 ∧ β ≠ 1 ∧ (∀ a ∈ A₀, β * a = a * β) ∧
        (∀ x ∈ R, (∀ a ∈ A₀, x * a = a * x) → ∃ c ∈ A₀, x = c ∨ x = c * β) ∧
        (∀ y ∈ R, (∀ a ∈ A₀, y * a * y⁻¹ ∈ A₀) → y * β = β * y) := by
  obtain ⟨ha, hb⟩ := andT kInS
  obtain ⟨qa, hqa, ea⟩ := L34Bo.inS_iff.1 ha
  obtain ⟨qb, hqb, eb⟩ := L34Bo.inS_iff.1 hb
  obtain ⟨a, haS, harep⟩ := enumerates_S.sound _ (S_mem hqa)
  obtain ⟨b, hbS, hbrep⟩ := enumerates_S.sound _ (S_mem hqb)
  rw [ea, L34N.K_tabs.1] at harep
  rw [eb, L34N.K_tabs.2.1] at hbrep
  have hrrep : TabRep (r₄T ()) r₄ := tabRep_r₄
  obtain ⟨ha3, hb3, hab, hdist, hr2, hr1, hra, hrb⟩ := small
  have ha3' : a ^ 3 = 1 := ((harep.pow 3).eq_iff TabRep.idTab).1 ha3
  have hb3' : b ^ 3 = 1 := ((hbrep.pow 3).eq_iff TabRep.idTab).1 hb3
  have hab' : a * b = b * a := ((harep.comp hbrep).eq_iff (hbrep.comp harep)).1 hab
  have hr2' : r₄ ^ 2 = 1 := by
    rw [pow_two]
    exact ((hrrep.comp hrrep).eq_iff TabRep.idTab).1 hr2
  have hr1' : r₄ ≠ 1 := fun h => hr1 ((hrrep.eq_iff TabRep.idTab).2 h)
  have hra' : r₄ * a = a * r₄ := ((hrrep.comp harep).eq_iff (harep.comp hrrep)).1 hra
  have hrb' : r₄ * b = b * r₄ := ((hrrep.comp hbrep).eq_iff (hbrep.comp hrrep)).1 hrb
  have hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)) := by
    intro k hk
    have : (e9T ())[k]! = comp 42 (powTab 42 a₀T (k / 3)) (powTab 42 b₀T (k % 3)) := by
      unfold e9T
      rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]
    rw [this]
    exact (harep.pow _).comp (hbrep.pow _)
  have hinj : ∀ k < 9, ∀ k' < 9, a ^ (k / 3) * b ^ (k % 3) = a ^ (k' / 3) * b ^ (k' % 3) →
      k = k' := fun k hk k' hk' he =>
    hdist k hk k' hk' (((hrepE k hk).eq_iff (hrepE k' hk')).2 he)
  set A₀ : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure {a, b} with hA₀
  have haA : a ∈ A₀ := Subgroup.subset_closure (Or.inl rfl)
  have hbA : b ∈ A₀ := Subgroup.subset_closure (Or.inr rfl)
  have hform : ∀ x ∈ A₀, ∃ k < 9, x = a ^ (k / 3) * b ^ (k % 3) := fun x hx =>
    ce_pair_form hab' ha3' hb3' hx
  have hmemE : ∀ k, a ^ (k / 3) * b ^ (k % 3) ∈ A₀ := fun k =>
    A₀.mul_mem (A₀.pow_mem haA _) (A₀.pow_mem hbA _)
  have hAS : A₀ ≤ S := (Subgroup.closure_le S).2 (by
    rintro _ (rfl | rfl)
    exacts [haS, hbS])
  have hcard : Nat.card A₀ = 9 := by
    have hrange : (A₀ : Set (Equiv.Perm (Fin 42))) =
        Set.range (fun k : Fin 9 => a ^ (k.val / 3) * b ^ (k.val % 3)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk, rfl⟩ := hform x hx
        exact ⟨⟨k, hk⟩, rfl⟩
      · rintro ⟨k, rfl⟩
        exact hmemE k.val
    have hf : Function.Injective (fun k : Fin 9 => a ^ (k.val / 3) * b ^ (k.val % 3)) :=
      fun k k' he => Fin.ext (hinj k.val k.2 k'.val k'.2 he)
    calc Nat.card A₀ = Nat.card (A₀ : Set (Equiv.Perm (Fin 42))) := rfl
      _ = Nat.card (Set.range (fun k : Fin 9 => a ^ (k.val / 3) * b ^ (k.val % 3))) := by
        rw [hrange]
      _ = Nat.card (Fin 9) := Nat.card_range_of_injective hf
      _ = 9 := by simp
  have hβ : ∀ c ∈ A₀, r₄ * c = c * r₄ := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := hform c hc
    have h1 : Commute r₄ a := hra'
    have h2 : Commute r₄ b := hrb'
    exact ((h1.pow_right _).mul_right (h2.pow_right _)).eq
  have hlist : ∀ {y : Equiv.Perm (Fin 42)} {i : ℕ}, i < 241920 →
      TabRep (unpack 42 6 (L34R.T i)) y → (∀ c ∈ A₀, y * c * y⁻¹ ∈ A₀) →
      ∃ q < 7755, L34N.J q / 32 = i ∧ L34N.J q % 2 = 1 := by
    intro y i hi hyrep hyn
    refine (L34N.normA_iff hi).1 ⟨?_, ?_⟩
    · obtain ⟨k, hk, hke⟩ := hform _ (hyn a haA)
      exact ⟨k, hk, ((hyrep.comp harep).eq_iff ((hrepE k hk).comp hyrep)).2
        (mul_inv_eq_iff_eq_mul.1 hke)⟩
    · obtain ⟨k, hk, hke⟩ := hform _ (hyn b hbA)
      exact ⟨k, hk, ((hyrep.comp hbrep).eq_iff ((hrepE k hk).comp hyrep)).2
        (mul_inv_eq_iff_eq_mul.1 hke)⟩
  refine ⟨A₀, hAS, hcard, r₄, r₄_mem_R, hr2', hr1', hβ, ?_, ?_⟩
  · intro x hxR hxc
    obtain ⟨i, hi, hxrep⟩ := L34N3.exists_T hxR
    have hxn : ∀ c ∈ A₀, x * c * x⁻¹ ∈ A₀ := fun c hc => by
      rw [hxc c hc, mul_inv_cancel_right]
      exact hc
    obtain ⟨q, hq, hqi, hodd⟩ := hlist hi hxrep hxn
    have h := ce_at hq hodd
    rw [hqi] at h
    unfold cePt at h
    obtain ⟨-, h⟩ := andT h
    rcases (CFSG.KC.L34KSnd.orB_iff.1 h) with h | h
    · exfalso
      have c1 : commPt 42 6 (L34R.T i) (L34N.K 0) = true := by
        rw [CFSG.KC.L34KSnd.commPt_iff (L34N.canonT hi) (L34N.canonK' (by decide)),
          L34N.K_tabs.1]
        exact ((hxrep.comp harep).eq_iff (harep.comp hxrep)).2 (hxc a haA)
      have c2 : commPt 42 6 (L34R.T i) (L34N.K 1) = true := by
        rw [CFSG.KC.L34KSnd.commPt_iff (L34N.canonT hi) (L34N.canonK' (by decide)),
          L34N.K_tabs.2.1]
        exact ((hxrep.comp hbrep).eq_iff (hbrep.comp hxrep)).2 (hxc b hbA)
      rw [CFSG.KC.L34KSnd.notB_iff, c1, c2] at h
      exact Bool.noConfusion h
    · obtain ⟨j, hj, h⟩ := CFSG.KC.L34Norm.anyN_iff.1 h
      rcases (CFSG.KC.L34KSnd.orB_iff.1 h) with h | h
      · have e := Nat.eq_of_beq_eq_true h
        have hrep' : TabRep (unpack 42 6 (L34R.T i)) (a ^ (j / 3) * b ^ (j % 3)) := by
          rw [e, L34N.K_tabs.2.2.2 j hj]
          exact hrepE j hj
        exact ⟨_, hmemE j, Or.inl (hxrep.perm_eq hrep')⟩
      · have e := Nat.eq_of_beq_eq_true h
        have hrep' : TabRep (unpack 42 6 (L34R.T i)) (r₄ * (a ^ (j / 3) * b ^ (j % 3))) := by
          rw [e, ← CFSG.KC.L34KSnd.comp_unpack' canonRP (L34N.canonAP hj), ← r4_eq,
            L34N.K_tabs.2.2.2 j hj]
          exact hrrep.comp (hrepE j hj)
        refine ⟨_, hmemE j, Or.inr ?_⟩
        rw [hxrep.perm_eq hrep', hβ _ (hmemE j)]
  · intro y hyR hyn
    obtain ⟨i, hi, hyrep⟩ := L34N3.exists_T hyR
    obtain ⟨q, hq, hqi, hodd⟩ := hlist hi hyrep hyn
    have h := ce_at hq hodd
    rw [hqi] at h
    unfold cePt at h
    have hc := (commPt_r4 hi).1 (andT h).1
    exact ((hyrep.comp hrrep).eq_iff (hrrep.comp hyrep)).1 hc

end CertificateChecks.KernelLC.L34Ce

end
