module

public import Certificates.Kernel.LocalComp.L34F946Chk
public import Certificates.Kernel.LocalComp.L34N3Final
public import CFSG.Certificates.Kernel.L34SelWordSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34F946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.KC.L34SelWord CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four
open CFSG.KLie.CT (fget andB orB notB anyN)

theorem canonS {j : ℕ} (hj : j < 20160) : canonK 42 6 (mask 6) (42 * 6) (L34S.T j) = true :=
  pinS.canon j hj

theorem S_lt {j : ℕ} (hj : j < 20160) :
    (enumBFS 42 gensS 20160).tabs[j]! = unpack 42 6 (L34S.T j) := by
  rw [hS.1]
  exact CFSG.KC.L34KSnd.pts_get hj

theorem S_rep {j : ℕ} (hj : j < 20160) :
    ∃ g ∈ S, TabRep (unpack 42 6 (L34S.T j)) g := by
  refine enumerates_S.sound _ ?_
  rw [← S_lt hj]
  exact getElem!_mem (by rw [hS.1, size_pts]; exact hj)

theorem mem_S_of_inS {s : ℕ} {X : ℕ} {x : Equiv.Perm (Fin 42)}
    (hx : TabRep (unpack 42 6 X) x) (h : inS s X = true) : x ∈ S := by
  unfold inS at h
  rw [CFSG.KC.L34KSnd.andB_iff] at h
  obtain ⟨g, hg, hr⟩ := S_rep (Nat.le_of_ble_eq_true h.1)
  rw [Nat.eq_of_beq_eq_true h.2] at hr
  rwa [hr.perm_eq hx] at hg

theorem kK_facts : inS (fK 0) (L34N.K 0) = true ∧ inS (fK 1) (L34N.K 1) = true ∧
    inS (fK 2) (L34N.K 2) = true ∧ o3Pt 42 6 (pidn 42 6) (L34N.K 0) = true ∧
    o3Pt 42 6 (pidn 42 6) (L34N.K 1) = true ∧ o3Pt 42 6 (pidn 42 6) (L34N.K 2) = true ∧
    commPt 42 6 (L34N.K 0) (L34N.K 1) = true ∧
    ∀ i < 9, ∀ j < 9, i = j ∨ L34N.AP i ≠ L34N.AP j := by
  have h := kK
  simp only [CFSG.KC.L34KSnd.andB_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun i hi j hj => ?_⟩
  have h9 := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h8 i hi) j hj
  rw [CFSG.KC.L34KSnd.orB_iff, CFSG.KC.L34KSnd.notB_iff] at h9
  rcases h9 with h9 | h9
  · exact Or.inl (Nat.eq_of_beq_eq_true h9)
  · exact Or.inr (Nat.ne_of_beq_eq_false h9)

theorem const_rep {j : ℕ} (hj : j < 3) :
    ∃ g ∈ S, TabRep (unpack 42 6 (L34N.K j)) g ∧ g ≠ 1 ∧ g ^ 3 = 1 := by
  have hin : inS (fK j) (L34N.K j) = true := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    exacts [kK_facts.1, kK_facts.2.1, kK_facts.2.2.1]
  have ho : o3Pt 42 6 (pidn 42 6) (L34N.K j) = true := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    exacts [kK_facts.2.2.2.1, kK_facts.2.2.2.2.1, kK_facts.2.2.2.2.2.1]
  have hin' := hin
  unfold inS at hin'
  rw [CFSG.KC.L34KSnd.andB_iff] at hin'
  obtain ⟨g, hg, hr⟩ := S_rep (Nat.le_of_ble_eq_true hin'.1)
  rw [Nat.eq_of_beq_eq_true hin'.2] at hr
  obtain ⟨h1, h3⟩ := (o3Pt_iff (L34N.canonK' (j := j) (by omega))).1 ho
  refine ⟨g, hg, hr, fun e => h1 ((hr.eq_iff TabRep.idTab).2 e), ?_⟩
  rw [pow_three]
  exact ((hr.comp (hr.comp hr)).eq_iff TabRep.idTab).1 h3

theorem mem_closure_pair_pow' {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) {x : G} (hx : x ∈ Subgroup.closure {a, b}) :
    ∃ i j : ℕ, x = a ^ i * b ^ j := by
  have hc : Commute a b := hab
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
    have : b ^ j * a ^ i' = a ^ i' * b ^ j := (hc.symm.pow_pow j i').eq
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
    have hcom : b ^ j * a ^ (2 * i) = a ^ (2 * i) * b ^ j := (hc.symm.pow_pow j (2 * i)).eq
    rw [inv_eq_iff_mul_eq_one]
    calc a ^ i * b ^ j * (a ^ (2 * i) * b ^ (2 * j))
        = a ^ i * (b ^ j * a ^ (2 * i)) * b ^ (2 * j) := by group
      _ = a ^ i * (a ^ (2 * i) * b ^ j) * b ^ (2 * j) := by rw [hcom]
      _ = (a ^ i * a ^ (2 * i)) * (b ^ j * b ^ (2 * j)) := by group
      _ = 1 := by rw [h1, h2, one_mul]

theorem pow_mod_three' {G : Type*} [Group G] {a : G} (ha : a ^ 3 = 1) (i : ℕ) :
    a ^ i = a ^ (i % 3) := by
  conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, ha, one_pow, mul_one]

theorem A₀_facts :
    ∃ a ∈ S, ∃ b ∈ S, TabRep (unpack 42 6 (L34N.K 0)) a ∧ TabRep (unpack 42 6 (L34N.K 1)) b ∧
      Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 42))) ≤ S ∧
      Nat.card (Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 42)))) = 9 ∧
      (∀ k < 9, TabRep (unpack 42 6 (L34N.AP k)) (a ^ (k / 3) * b ^ (k % 3))) ∧
      ∀ x ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 42))),
        ∃ k < 9, x = a ^ (k / 3) * b ^ (k % 3) := by
  obtain ⟨a, haS, ha, -, ha3⟩ := const_rep (j := 0) (by decide)
  obtain ⟨b, hbS, hb, -, hb3⟩ := const_rep (j := 1) (by decide)
  have hab : a * b = b * a := by
    have h := (CFSG.KC.L34KSnd.commPt_iff (L34N.canonK' (j := 0) (by decide))
      (L34N.canonK' (j := 1) (by decide))).1 kK_facts.2.2.2.2.2.2.1
    exact ((ha.comp hb).eq_iff (hb.comp ha)).1 h
  have ha' : TabRep a₀T a := by rw [← L34N.K_tabs.1]; exact ha
  have hb' : TabRep b₀T b := by rw [← L34N.K_tabs.2.1]; exact hb
  have hrepE : ∀ k < 9, TabRep (unpack 42 6 (L34N.AP k)) (a ^ (k / 3) * b ^ (k % 3)) := by
    intro k hk
    rw [L34N.K_tabs.2.2.2 k hk]
    have : (e9T ())[k]! = comp 42 (powTab 42 a₀T (k / 3)) (powTab 42 b₀T (k % 3)) := by
      unfold e9T
      rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]
    rw [this]
    exact (ha'.pow _).comp (hb'.pow _)
  have hinj : ∀ k < 9, ∀ k' < 9, a ^ (k / 3) * b ^ (k % 3) = a ^ (k' / 3) * b ^ (k' % 3) →
      k = k' := by
    intro k hk k' hk' he
    rcases kK_facts.2.2.2.2.2.2.2 k hk k' hk' with h | h
    · exact h
    · refine absurd (CFSG.KC.L34KSnd.unpack_inj' (L34N.canonAP hk) (L34N.canonAP hk') ?_) h
      have h2 := hrepE k' hk'
      rw [← he] at h2
      exact (hrepE k hk).tab_eq h2
  set A₀ : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure {a, b}
  have haA : a ∈ A₀ := Subgroup.subset_closure (Or.inl rfl)
  have hbA : b ∈ A₀ := Subgroup.subset_closure (Or.inr rfl)
  have hform : ∀ x ∈ A₀, ∃ k < 9, x = a ^ (k / 3) * b ^ (k % 3) := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := mem_closure_pair_pow' hab ha3 hb3 hx
    refine ⟨3 * (i % 3) + j % 3, by omega, ?_⟩
    have e1 : (3 * (i % 3) + j % 3) / 3 = i % 3 := by omega
    have e2 : (3 * (i % 3) + j % 3) % 3 = j % 3 := by omega
    rw [e1, e2, ← pow_mod_three' ha3, ← pow_mod_three' hb3]
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
        exact A₀.mul_mem (A₀.pow_mem haA _) (A₀.pow_mem hbA _)
    have hf : Function.Injective (fun k : Fin 9 => a ^ (k.val / 3) * b ^ (k.val % 3)) :=
      fun k k' he => Fin.ext (hinj k.val k.2 k'.val k'.2 he)
    calc Nat.card A₀ = Nat.card (A₀ : Set (Equiv.Perm (Fin 42))) := rfl
      _ = Nat.card (Set.range (fun k : Fin 9 => a ^ (k.val / 3) * b ^ (k.val % 3))) := by
        rw [hrange]
      _ = Nat.card (Fin 9) := Nat.card_range_of_injective hf
      _ = 9 := by simp
  exact ⟨a, haS, b, hbS, ha, hb, hAS, hcard, hrepE, hform⟩

theorem listed_of {B : ℕ → Bool} (hB : B 0 = false) {i : ℕ} (hi : i < 241920)
    (h : B (L34N.code (pidn 42 6) i) = true) :
    ∃ q < 7755, L34N.J q / 32 = i ∧ B (L34N.J q % 32) = true :=
  (L34N.listed_iff hB hi).1 h

theorem code_div8_ne {i : ℕ} (hi : i < 241920) {x : Equiv.Perm (Fin 42)}
    (hx : TabRep (unpack 42 6 (L34R.T i)) x) (h1 : x ≠ 1) (h3 : x ^ 3 = 1) :
    L34N.code (pidn 42 6) i / 8 ≠ 0 := by
  rw [L34N.code_eq, (normCode_bits ..).2.2.2]
  intro e
  have hf := (o3Cat_spec 42 6 (pidn 42 6) (L34R.T i)).1.1 e
  have ht := (L34N.o3_iff hi).2 ⟨fun e' => h1 ((hx.eq_iff TabRep.idTab).1 e'),
    ((hx.comp (hx.comp hx)).eq_iff TabRep.idTab).2 (by rw [← pow_three]; exact h3)⟩
  exact Bool.false_ne_true (hf.symm.trans ht)

theorem conj_tab {X G E : Tab} {x g e : Equiv.Perm (Fin 42)} (hx : TabRep X x) (hg : TabRep G g)
    (he : TabRep E e) : comp 42 X G = comp 42 E X ↔ x * g * x⁻¹ = e := by
  rw [(hx.comp hg).eq_iff (he.comp hx)]
  constructor
  · intro h
    rw [h]
    group
  · intro h
    rw [← h]
    group

theorem spec9460 :
    ∃ T₀ : Subgroup (Equiv.Perm (Fin 42)), T₀ ≤ S ∧ Nat.card T₀ = 9 ∧
      ∀ x ∈ R, x ^ 3 = 1 → x ∉ S → (∀ t ∈ T₀, x * t * x⁻¹ ∈ T₀) →
        ∃ c ∈ S, c * x = x * c ∧ ∃ t ∈ T₀, c * t * c⁻¹ ∉ T₀ := by
  obtain ⟨a, -, b, -, ha, hb, hAS, hcard, hrepE, hform⟩ := A₀_facts
  set A₀ : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure {a, b}
  have haA : a ∈ A₀ := Subgroup.subset_closure (Or.inl rfl)
  have hbA : b ∈ A₀ := Subgroup.subset_closure (Or.inr rfl)
  refine ⟨A₀, hAS, hcard, fun x hxR hx3 hxS hxN => ?_⟩
  obtain ⟨i, hi, hx⟩ := L34N3.exists_T hxR
  have hx1 : x ≠ 1 := fun e => hxS (e ▸ S.one_mem)
  have hnorm : ∀ {g : Equiv.Perm (Fin 42)} {G : ℕ}, TabRep (unpack 42 6 G) g → g ∈ A₀ →
      ∃ j < 9, comp 42 (unpack 42 6 (L34R.T i)) (unpack 42 6 G) =
        comp 42 (unpack 42 6 (L34N.AP j)) (unpack 42 6 (L34R.T i)) := by
    intro g G hg hgA
    obtain ⟨k, hk, hke⟩ := hform _ (hxN g hgA)
    exact ⟨k, hk, (conj_tab hx hg (hrepE k hk)).2 hke⟩
  have hodd : L34N.code (pidn 42 6) i % 2 = 1 := by
    obtain ⟨j, hj, hja⟩ := hnorm ha haA
    obtain ⟨j', hj', hjb⟩ := hnorm hb hbA
    rw [L34N.K_tabs.1] at hja
    rw [L34N.K_tabs.2.1] at hjb
    rw [L34N.K_tabs.2.2.2 j hj] at hja
    rw [L34N.K_tabs.2.2.2 j' hj'] at hjb
    obtain ⟨q, hq, hqi, hJ⟩ := (L34N.normA_iff hi).1 ⟨⟨j, hj, hja⟩, ⟨j', hj', hjb⟩⟩
    have h := (L34N.listed_iff (B := fun v => Nat.beq (v % 2) 1) rfl hi).2
      ⟨q, hq, hqi, by
        change Nat.beq (L34N.J q % 32 % 2) 1 = true
        rw [Nat.beq_eq]
        omega⟩
    exact Nat.eq_of_beq_eq_true h
  have hP : predA (L34N.code (pidn 42 6) i) = true := by
    unfold predA
    rw [CFSG.KC.L34KSnd.andB_iff, CFSG.KC.L34KSnd.notB_iff, Nat.beq_eq]
    exact ⟨hodd, beq_false (code_div8_ne hi hx hx1 hx3)⟩
  obtain ⟨q, hq, hqi, hPq⟩ := listed_of (B := predA) rfl hi hP
  obtain ⟨m, -, -, hok⟩ := selK_sound kA hq hPq
  rw [hqi] at hok
  unfold okA at hok
  rw [strictB_eq, CFSG.KC.L34KSnd.orB_iff] at hok
  rcases hok with hin | hok
  · exact absurd (mem_S_of_inS hx hin) hxS
  rw [strictB_eq, CFSG.KC.L34KSnd.andB_iff] at hok
  obtain ⟨hjlt, hok⟩ := hok
  have hj := Nat.le_of_ble_eq_true hjlt
  rw [strictB_eq, CFSG.KC.L34KSnd.andB_iff, CFSG.KC.L34KSnd.orB_iff,
    CFSG.KC.L34KSnd.notB_iff, CFSG.KC.L34KSnd.notB_iff] at hok
  obtain ⟨hcomm, hnot⟩ := hok
  obtain ⟨c, hcS, hc⟩ := S_rep hj
  refine ⟨c, hcS, ((hc.comp hx).eq_iff (hx.comp hc)).1
    ((CFSG.KC.L34KSnd.commPt_iff (canonS hj) (L34N.canonT hi)).1 hcomm), ?_⟩
  have hout : ∀ {g : Equiv.Perm (Fin 42)} {jj : ℕ}, jj < 2 → TabRep (unpack 42 6 (L34N.K jj)) g →
      inPts 42 6 9 L34N.AP (L34S.T (fget (WA m) 2 32)) (L34N.K jj) = false → c * g * c⁻¹ ∉ A₀ := by
    intro g jj hjj hg hf hmem
    obtain ⟨k, hk, hke⟩ := hform _ hmem
    have h := (inPts_iff (canonS hj) (L34N.canonK' (j := jj) (by omega))
      (fun j hj => L34N.canonAP hj)).2 ⟨k, hk, (conj_tab hc hg (hrepE k hk)).2 hke⟩
    exact absurd (h.symm.trans hf) (by decide)
  rcases hnot with h | h
  · exact ⟨a, haA, hout (by decide) ha h⟩
  · exact ⟨b, hbA, hout (by decide) hb h⟩

end CertificateChecks.KernelLC.L34F946

end
