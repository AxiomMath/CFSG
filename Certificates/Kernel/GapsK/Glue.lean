module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Main
public import CFSG.Certificates.Kernel.GapsKSound
public import CFSG.Certificates.Kernel.WCKSound
public import Certificates.Certificate21102
import Certificates.Kernel.GapsK.Checks
import Certificates.Kernel.WCK2.Checks
public import CFSG.CGT.Timmesfeld75.ListWCMathieu

public section

namespace CertificateChecks.KernelGapsK

open CFSG.KC.GapsK CFSG.KC.S97RYK CFSG.KC.WCK CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75
open CFSG.CGT.Timmesfeld75.WCCheck CFSG.RankThree.GF2n.Tim81 CFSG.RankThree.GF2n.Tim81.Gaps
open CFSG.Blueprint CFSG.LargeExtraspecial.S11.PairCheck

private theorem a6_mem (l : Int) : a6GData.D.gens l ∈ [a6tA, a6tAi, a6tB, a6tBi, idT 6] := by
  change a6gens l ∈ _
  unfold a6gens
  split_ifs <;> simp

private theorem a7_mem (l : Int) : a7GData.D.gens l ∈ [a7tA, a7tAi, a7tB, a7tBi, idT 7] := by
  change a7gens l ∈ _
  unfold a7gens
  split_ifs <;> simp

private theorem a8_mem (l : Int) : a8GData.D.gens l ∈ [a8tA, a8tAi, a8tB, a8tBi, idT 8] := by
  change a8gens l ∈ _
  unfold a8gens
  split_ifs <;> simp

private theorem a9_mem (l : Int) : a9GData.D.gens l ∈ [a9tA, a9tAi, a9tB, a9tBi, idT 9] := by
  change a9gens l ∈ _
  unfold a9gens
  split_ifs <;> simp

private theorem m22_mem (l : Int) :
    m22GData.D.gens l ∈ [m22tA, m22tAi, m22tB, m22tBi, idT 22] := by
  change m22gens l ∈ _
  unfold m22gens
  split_ifs <;> simp

private theorem m23_mem (l : Int) :
    m23GData.D.gens l ∈ [m23tA, m23tAi, m23tB, m23tBi, idT 23] := by
  change m23gens l ∈ _
  unfold m23gens
  split_ifs <;> simp

private theorem m24_mem (l : Int) :
    m24GData.D.gens l ∈ [m24tA, m24tAi, m24tB, m24tBi, idT 24] := by
  change m24gens l ∈ _
  unfold m24gens
  split_ifs <;> simp

theorem subpairWitness_alt6K : SubpairWitness (alternatingGroup (Fin 6)) :=
  subpairWitness_of_gapsK (P := a6GData) (M := alternatingGroup (Fin 6)) rep_a6gen a6gen_neg
    ⟨45, by decide, card_alt6⟩ (gens_valid a6_mem a6_gens)
    (baseCheck_of_gapsBaseK (gens_valid a6_mem a6_gens) a6_base) a6_ok

theorem subpairWitness_alt7K : SubpairWitness (alternatingGroup (Fin 7)) :=
  subpairWitness_of_gapsK (P := a7GData) (M := alternatingGroup (Fin 7)) rep_a7gen a7gen_neg
    ⟨315, by decide, card_alt7⟩ (gens_valid a7_mem a7_gens)
    (baseCheck_of_gapsBaseK (gens_valid a7_mem a7_gens) a7_base) a7_ok

theorem subpairWitness_alt8K : SubpairWitness (alternatingGroup (Fin 8)) :=
  subpairWitness_of_gapsK (P := a8GData) (M := alternatingGroup (Fin 8)) rep_a8gen a8gen_neg
    ⟨315, by decide, card_alt8⟩ (gens_valid a8_mem a8_gens)
    (baseCheck_of_gapsBaseK (gens_valid a8_mem a8_gens) a8_base) a8_ok

theorem subpairWitness_alt9K : SubpairWitness (alternatingGroup (Fin 9)) :=
  subpairWitness_of_gapsK (P := a9GData) (M := alternatingGroup (Fin 9)) rep_a9gen a9gen_neg
    ⟨2835, by decide, card_alt9⟩ (gens_valid a9_mem a9_gens)
    (baseCheck_of_gapsBaseK (gens_valid a9_mem a9_gens) a9_base) a9_ok

private theorem m22_base : baseCheck m22GData.D = true := by
  have h := Certificates.certificate21102.1
  rw [wcCheck_eq, Bool.and_eq_true] at h
  exact h.1

private theorem m23_base : baseCheck m23GData.D = true := by
  have h := Certificates.certificate21102.2.1
  rw [wcCheck_eq, Bool.and_eq_true] at h
  exact h.1

private theorem m24_base : baseCheck m24GData.D = true := by
  have h := Certificates.certificate21102.2.2
  rw [wcCheck_eq, Bool.and_eq_true] at h
  exact h.1

theorem subpairWitness_m22K :
    SubpairWitness NativeSporadic.M22 :=
  subpairWitness_of_gapsK (P := m22GData) (M := NativeSporadic.M22) rep_m22gen m22gen_neg
    ⟨3465, by decide, card_m22⟩ (gens_valid m22_mem KernelWCK2.m22_gens) m22_base m22_ok

theorem subpairWitness_m23K :
    SubpairWitness NativeSporadic.M23 :=
  subpairWitness_of_gapsK (P := m23GData) (M := NativeSporadic.M23) rep_m23gen m23gen_neg
    ⟨79695, by decide, card_m23⟩ (gens_valid m23_mem KernelWCK2.m23_gens) m23_base m23_ok

theorem subpairWitness_m24K :
    SubpairWitness NativeSporadic.M24 :=
  subpairWitness_of_gapsK (P := m24GData) (M := NativeSporadic.M24) rep_m24gen m24gen_neg
    ⟨239085, by decide, card_m24⟩ (gens_valid m24_mem KernelWCK2.m24_gens) m24_base m24_ok

theorem gapsStatementK :
    GapsStatement := by
  intro X _ hX
  rcases hX with hAlt | hM22 | hM23 | hM24
  · obtain ⟨k, h6, h9, ⟨e⟩⟩ := hAlt
    interval_cases k
    · exact SubpairWitness.of_mulEquiv e subpairWitness_alt6K
    · exact SubpairWitness.of_mulEquiv e subpairWitness_alt7K
    · exact SubpairWitness.of_mulEquiv e subpairWitness_alt8K
    · exact SubpairWitness.of_mulEquiv e subpairWitness_alt9K
  · obtain ⟨e⟩ := hM22
    exact SubpairWitness.of_mulEquiv e subpairWitness_m22K
  · obtain ⟨e⟩ := hM23
    exact SubpairWitness.of_mulEquiv e subpairWitness_m23K
  · obtain ⟨e⟩ := hM24
    exact SubpairWitness.of_mulEquiv e subpairWitness_m24K

end CertificateChecks.KernelGapsK

end
