module

public import Certificates.Kernel.Sporadic.Fi24Sev.Sylow
public import Certificates.Kernel.Sporadic.Fi24Sev.Core
public import Certificates.Kernel.Sporadic.Fi24Sev.Three

public section

namespace CFSG.KD.Fi24Sev.Final

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative CFSG.KD.Fi24ThreeO.Group


theorem cj_lt : ∀ c ∈ CFSG.KD.Fi24SevB.cj, ∀ l ∈ c.2.2.1, l < 2 * 1087 := by decide +kernel

theorem conj_lt : ∀ t ∈ conjTs, ∀ l ∈ (fi24SevenData.conj[t]!).2, l < 2 * 1087 := by
  intro t ht
  change t ∈ [3, 21, 49, 56, 63, 70, 77, 84, 91] at ht
  rw [← CFSG.KD.Fi24Sev.SevenB.cj_ts, List.mem_map] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  obtain ⟨hlt, hC7, -⟩ := CFSG.KD.Fi24Sev.SevenB.cj_data c hc
  have hconj : fi24SevenData.conj[c.1]! = (c.2.1, c.2.2.1) := by
    rw [CertificateChecks.KernelF24S.conj_eq, ← hC7,
      getElem!_pos _ c.1 (by simp [CertificateChecks.KernelF24S.c7_len]; omega)]
    simp only [List.getElem_toArray]
    rw [List.getD_eq_getElem _ _ (by rw [CertificateChecks.KernelF24S.c7_len]; omega)]
  rw [hconj]
  exact cj_lt c hc

theorem sevenFacts (hB : Bridge) : SevenFacts := by
  obtain ⟨hx7, hy7, hc, hcx, hcy, -⟩ := CFSG.KD.Fi24Sev.SevenB.cube_facts hB
  have hinj := CFSG.KD.Fi24Sev.Sylow.inj hB
  exact
    { pow_x := hx7
      pow_y := hy7
      comm := hc
      comm_x := hcx
      comm_y := hcy
      inj := hinj
      conj := CFSG.KD.Fi24Sev.Sylow.conj hB
      card_y := CFSG.KD.Fi24Sev.Seven.card_centralizer_y hB
      card_c := CFSG.KD.Fi24Sev.Seven.card_centralizer_c hB
      core_y := CFSG.KD.Fi24Sev.Core.core_y hB hinj
      core_c := CFSG.KD.Fi24Sev.Core.core_c hB hinj
      conj_lt := conj_lt
      rel := fun _ ht => CFSG.KD.Fi24Sev.SevenB.conj_facts hB ht }

theorem centFacts (hB : Bridge) : CentFacts :=
  CFSG.KD.Fi24Sev.Three.centFacts hB (fun _ hg => CFSG.KD.Fi24Sev.Sylow.pow_seven hB hg)

end CFSG.KD.Fi24Sev.Final

end
