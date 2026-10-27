module

public import Certificates.Data.Item434G28R
public import Certificates.Kernel.G28.R9549
public import CFSG.Certificates.Kernel.G28.R2Facts
public import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CertificateChecks.KernelG28.R9549

open CFSG.KC.G28R CFSG.KC.Misc.Clos CFSG.RankThree.PartTwo.Sec4.Item434G28

theorem tAll : ∀ i < 12096, treeAt m2K idK RG 4 RE RP i = true :=
  forall_of_chunks 1008 12 _ fun c hc => TK.all c hc

theorem cAll : ∀ i < 12096, closedAt m2K RG 4 12096 RE RC i = true :=
  forall_of_chunks 252 48 _ fun c hc => CK.all c hc

theorem eAll : ∀ i < 12096, elemAt RE RW RI RT 12096 i = true :=
  forall_of_chunks 168 72 _ fun c hc => EK.all c hc

theorem rAll : ∀ r < 2, repAt RI RT RCC r = true := RK.all

theorem rg_eq : RG 0 = rGenXb ∧ RG 1 = rGenXa ∧ RG 2 = rGenYa ∧ RG 3 = rGenYb := by
  decide +kernel

theorem hG : ∀ j < rGens.length, RG j = rGens.getD j 0 := by
  intro j hj
  have hj4 : j < 4 := hj
  interval_cases j
  · exact rg_eq.1
  · exact rg_eq.2.1
  · exact rg_eq.2.2.1
  · exact rg_eq.2.2.2

theorem letters : letterBin (8 * 5 + 1) rGenXb = true ∧ letterBin (8 * 0 + 1) rGenXa = true ∧
    letterBin (8 * 6 + 1) rGenYa = true ∧ letterBin (8 * 11 + 1) rGenYb = true := by
  decide +kernel

theorem proof9549 : ∀ R : Submonoid (Matrix (Fin 6) (Fin 6) CFSG.Quasithin.GF8),
    R = Submonoid.closure {x | ∃ g ∈ rGens, dec2 g = x} →
    (∀ e ∈ R, ∀ y ∈ R, e ^ 3 = 1 → e ≠ 1 → y ^ 7 = 1 → y ≠ 1 → e * y ≠ y * e) ∧
    (∀ e ∈ R, ∀ t ∈ R, ∀ t' ∈ R, e ^ 3 = 1 → e ≠ 1 → t ^ 2 = 1 → t ≠ 1 → t' ^ 2 = 1 →
      t' ≠ 1 → t ≠ t' → t * e = e * t → t' * e = e * t' → t * t' = t' * t → False) ∧
    (∀ e ∈ R, ∀ u ∈ R, ∀ t ∈ R, e ^ 3 = 1 → e ≠ 1 → u ^ 3 = 1 → u ≠ 1 → u ≠ e →
      u ≠ e * e → t ^ 2 = 1 → t ≠ 1 → t * e = e * t → t * u = u * t → u * e = e * u → False) ∧
    decode (letterCode (8 * 5 + 1)) = dec2 rGenXb ∧ decode (letterCode (8 * 0 + 1)) = dec2 rGenXa ∧
    decode (letterCode (8 * 6 + 1)) = dec2 rGenYa ∧
    decode (letterCode (8 * 11 + 1)) = dec2 rGenYb := by
  rintro R rfl
  obtain ⟨l1, l2, l3, l4⟩ := letters
  obtain ⟨f3, f2, f1⟩ := facts_of (gens := rGens) hG (by norm_num) tAll cAll eAll rAll
  exact ⟨f3, f2, f1, decode_letterCode_eq_dec2 l1, decode_letterCode_eq_dec2 l2,
    decode_letterCode_eq_dec2 l3, decode_letterCode_eq_dec2 l4⟩

end CertificateChecks.KernelG28.R9549

end
