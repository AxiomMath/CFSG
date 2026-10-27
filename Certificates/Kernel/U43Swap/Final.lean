module

public import Certificates.Kernel.U43Swap.Facts
public import Certificates.Kernel.U43Swap.Glue
public import Certificates.Kernel.ThCent.Leaves

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.KernelU43Swap

open CFSG.OddStandard.SmallF3.Omega CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2
  CFSG.Quasithin.H13.U43 Certificates.Asc82Swap CFSG.KS.U43Swap CertificateChecks.KernelU43Mod


theorem psi_mem_H4 {s : X₀} (hs : s ∈ SwC) : psi s ∈ H4 := by
  obtain ⟨f, hf, -, himg⟩ := sw_elemList_enum
  have hs' : s ∈ f '' Set.Iio (elemList 820 tabA tabB).size := by
    rw [himg]
    exact hs
  obtain ⟨i, hi, rfl⟩ := hs'
  obtain ⟨x, hx, hrx⟩ := h4_enum.2.1 i hi
  rw [(hf i hi).unique hrx]
  exact hx

theorem exists_of_mem_H4 {x : Equiv.Perm (Fin 820)} (hx : x ∈ H4) : ∃ s ∈ SwC, psi s = x := by
  obtain ⟨f, hf, -, himg⟩ := sw_elemList_enum
  obtain ⟨i, hi, hri⟩ := h4_enum.2.2 x hx
  have hm : f i ∈ (SwC : Set X₀) := by
    rw [← himg]
    exact ⟨i, hi, rfl⟩
  exact ⟨f i, hm, (hf i hi).unique hri⟩

theorem psi_pow9 {s : X₀} : psi s ^ 9 = 1 ↔ s ^ 9 = 1 := by
  rw [← map_pow, ← map_one psi, psi_inj.eq_iff]

theorem odd_iff {s : X₀} (hs : s ∈ SwC) : Odd (orderOf s) ↔ psi s ^ 9 = 1 := by
  rw [psi_pow9]
  exact sw_odd_iff_pow9 (stage2HModel_card).2 hs

theorem swCen_iff {g h : X₀} : h ∈ SwCen g ↔ psi h ∈ PCen H4 (psi g) := by
  constructor
  · rintro ⟨hh, hc⟩
    refine ⟨psi_mem_H4 hh, fun o ho h9 => ?_⟩
    obtain ⟨o', ho', rfl⟩ := exists_of_mem_H4 ho
    have := congrArg psi (hc o' ho' ((odd_iff ho').2 h9))
    simpa only [map_mul, map_inv] using this
  · rintro ⟨hh, hc⟩
    obtain ⟨h', hh', he⟩ := exists_of_mem_H4 hh
    rw [psi_inj he] at hh'
    refine ⟨hh', fun o ho hodd => psi_inj ?_⟩
    have := hc (psi o) (psi_mem_H4 ho) ((odd_iff ho).1 hodd)
    simpa only [map_mul, map_inv] using this

theorem swTables : SwTables := by
  intro g₁ hg₁ g₂ hg₂ ho₁ ho₂ hn₁ hn₂ hm₁ hm₂
  have hne : ∀ {g : X₀}, g ≠ 1 → psi g ≠ 1 := fun hg e => hg (psi_inj (e.trans (map_one psi).symm))
  obtain ⟨hT1, c, hc, hX1, hX2⟩ := swFacts.tables (psi_mem_H4 hg₁) (psi_mem_H4 hg₂)
    ((odd_iff hg₁).1 ho₁) ((odd_iff hg₂).1 ho₂) (hne hn₁) (hne hn₂) (swCen_iff.1 hm₁)
    (swCen_iff.1 hm₂)
  obtain ⟨c', hc', rfl⟩ := exists_of_mem_H4 hc
  refine ⟨fun h h1 h2 => ?_, c', hc', fun o ho hodd hoC => ?_, fun o ho hodd hoC => ?_⟩
  · rcases hT1 (psi h) (swCen_iff.1 h1) (swCen_iff.1 h2) with e | e
    · exact Or.inl (psi_inj (e.trans (map_one psi).symm))
    · exact Or.inr (psi_inj (e.trans CP_zero))
  · have := hX1 (psi o) (psi_mem_H4 ho) ((odd_iff ho).1 hodd) (swCen_iff.1 hoC)
    rw [swCen_iff, map_mul, map_mul, map_inv]
    exact this
  · have := hX2 (psi o) (psi_mem_H4 ho) ((odd_iff ho).1 hodd) (swCen_iff.1 hoC)
    rw [swCen_iff, map_mul, map_mul, map_inv]
    exact this

theorem map_cent (y : X₀) : (SwC ⊓ Subgroup.centralizer ({y} : Set X₀)).map psi =
    H4 ⊓ Subgroup.centralizer ({psi y} : Set (Equiv.Perm (Fin 820))) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzC, hzy⟩ := Subgroup.mem_inf.1 hz
    refine Subgroup.mem_inf.2 ⟨psi_mem_H4 hzC, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hzy]
  · intro hx
    obtain ⟨hxH, hxy⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨z, hz, rfl⟩ := exists_of_mem_H4 hxH
    refine ⟨z, Subgroup.mem_inf.2 ⟨hz, Subgroup.mem_centralizer_singleton_iff.2 (psi_inj ?_)⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hxy

theorem oddCentFact : ∀ y ∈ SwC, Odd (orderOf y) → y ≠ 1 →
    Nat.card ↥(SwC ⊓ Subgroup.centralizer ({y} : Set X₀)) % 16 ≠ 0 := by
  intro y hy hodd hn
  have h := swFacts.oddCard (psi_mem_H4 hy) ((odd_iff hy).1 hodd)
    (fun e => hn (psi_inj (e.trans (map_one psi).symm)))
  rw [← Subgroup.card_map_of_injective psi_inj, map_cent]
  exact h

end CertificateChecks.KernelU43Swap

end
