module

public import CFSG.Certificates.Kernel.MonsterPcFive.CensusConj
public import Certificates.Kernel.MonsterPcFive.W425001
public import Certificates.Kernel.MonsterPcFive.CensusData
import Certificates.Kernel.MonsterPcFive.Tab
import Certificates.Kernel.MonsterPcFive.CensusCos
import Certificates.Kernel.MonsterPcFive.CensusRep
import Certificates.Kernel.MonsterPcFive.CensusFus

public section

namespace CertificateChecks.KernelMonPcFive

open CFSG.KC.MonPcFive CFSG.KC.MonPcFiveD
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus (prodAsc)
open _root_.Timmesfeld.PcFive (pw cw repIdx auts)
open _root_.Timmesfeld.PcReg (digitsOf)

theorem aut_dig : ∀ j < 3, ∀ i < 9,
    (vecV (dig9 (auts[j]!)[i]!)).beq (dec (nthN (autW j) i)) = true := by
  decide +kernel

theorem auts_size : auts.size = 3 := by decide +kernel

theorem cos_all : ∀ k < 3125, ∃ d, cosOK rcs k d = true := by
  obtain ⟨l0, l1, l2, l3, l4, -⟩ := m5CosLen
  have ch : ∀ {lo : ℕ} {ds : List ℕ}, cosRun rcs lo ds = true → ds.length = 625 →
      ∀ k, lo ≤ k → k < lo + 625 → ∃ d, cosOK rcs k d = true := by
    intro lo ds h hl k h1 h2
    have e := cosRun_spec h (k - lo) (by omega)
    rw [Nat.add_sub_cancel' h1] at e
    exact ⟨_, e⟩
  intro k hk
  rcases Nat.lt_or_ge k 625 with h | h
  · exact ch m5Cos0 l0 k (by omega) (by omega)
  rcases Nat.lt_or_ge k 1250 with h' | h'
  · exact ch m5Cos1 l1 k h (by omega)
  rcases Nat.lt_or_ge k 1875 with h'' | h''
  · exact ch m5Cos2 l2 k h' (by omega)
  rcases Nat.lt_or_ge k 2500 with h''' | h'''
  · exact ch m5Cos3 l3 k h'' (by omega)
  · exact ch m5Cos4 l4 k h''' (by omega)

theorem rep_all : ∀ ρ < 245, RepGood rcs rep 916 ρ := by
  have ch : ∀ {lo : ℕ} {hs ps : List ℕ}, repsRun rcs rep 916 lo 35 hs ps = true →
      ∀ ρ, lo ≤ ρ → ρ < lo + 35 → RepGood rcs rep 916 ρ := by
    intro lo hs ps h ρ h1 h2
    have e := repsRun_spec h (ρ - lo) (by omega)
    rwa [Nat.add_sub_cancel' h1] at e
  intro ρ hρ
  rcases Nat.lt_or_ge ρ 35 with h0 | h0
  · exact ch m5Rep0 ρ (by omega) (by omega)
  rcases Nat.lt_or_ge ρ 70 with h1 | h1
  · exact ch m5Rep1 ρ h0 (by omega)
  rcases Nat.lt_or_ge ρ 105 with h2 | h2
  · exact ch m5Rep2 ρ h1 (by omega)
  rcases Nat.lt_or_ge ρ 140 with h3 | h3
  · exact ch m5Rep3 ρ h2 (by omega)
  rcases Nat.lt_or_ge ρ 175 with h4 | h4
  · exact ch m5Rep4 ρ h3 (by omega)
  rcases Nat.lt_or_ge ρ 210 with h5 | h5
  · exact ch m5Rep5 ρ h4 (by omega)
  · exact ch m5Rep6 ρ h5 (by omega)

theorem fus_all : ∀ c < 916, classW rep depth kind arg cls wit 916 c = true := by
  have ch : ∀ {lo : ℕ}, fusW rep depth kind arg cls wit 916 lo 229 = true →
      ∀ c, lo ≤ c → c < lo + 229 → classW rep depth kind arg cls wit 916 c = true := by
    intro lo h c h1 h2
    have e := allBelow_spec h (c - lo) (by omega)
    rwa [Nat.add_sub_cancel' h1] at e
  intro c hc
  rcases Nat.lt_or_ge c 229 with h0 | h0
  · exact ch m5Fus0 c (by omega) (by omega)
  rcases Nat.lt_or_ge c 458 with h1 | h1
  · exact ch m5Fus1 c h0 (by omega)
  rcases Nat.lt_or_ge c 687 with h2 | h2
  · exact ch m5Fus2 c h1 (by omega)
  · exact ch m5Fus3 c h2 (by omega)

theorem psi_genV_g {G : Type*} [Group G] (g : Fin 9 → G) {i : ℕ} (hi : i < 9) :
    psi (g 0) (g 1) (bG g) (g 8) (genV i) = g ⟨i, hi⟩ := by
  interval_cases i
  · exact psi_genV0
  · exact psi_genV1
  · exact psi_genVb (b := bG g) 0
  · exact psi_genVb (b := bG g) 1
  · exact psi_genVb (b := bG g) 2
  · exact psi_genVb (b := bG g) 3
  · exact psi_genVb (b := bG g) 4
  · exact psi_genVb (b := bG g) 5
  · exact psi_genV8

theorem fiveCensusConj {G : Type} [Group G] [Finite G] {m : ℕ} (hcard : Nat.card G = 5 ^ 9 * m)
    (hm : ¬ 5 ∣ m) (g : Fin 9 → G)
    (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
    (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!)
    (hz : g 8 ≠ 1)
    (hN : ∀ j < auts.size, ∃ c : G, ∀ (i : ℕ) (hi : i < 9),
      c * g ⟨i, hi⟩ * c⁻¹ = prodAsc g (digitsOf 5 9 (auts[j]!)[i]!)) :
    ∀ s : G, orderOf s = 5 → ∃ k < repIdx.size, prodAsc g (digitsOf 5 9 repIdx[k]!) ^ 5 = 1 ∧
      ∃ e : ℕ, 0 < e ∧ e < 5 ∧ ∃ c : G, c * s * c⁻¹ = prodAsc g (digitsOf 5 9 repIdx[k]!) ^ e := by
  have H := pcHyp_of_rel hpow hcomm
  have hN' : ∀ j < 3, ∃ c : G, ∀ i < 9, c * psi (g 0) (g 1) (bG g) (g 8) (genV i) * c⁻¹ =
      psi (g 0) (g 1) (bG g) (g 8) (dec (nthN (autW j) i)) := by
    intro j hj
    obtain ⟨c, hc⟩ := hN j (by rw [auts_size]; exact hj)
    refine ⟨c, fun i hi => ?_⟩
    rw [psi_genV_g g hi, hc i hi, digitsOf_dig9, prodAsc_eq_psi, V9.beq_eq (aut_dig j hj i hi)]
  intro s hs
  obtain ⟨k, hk, hT, e, he0, he5, c, hc⟩ :=
    census_conj H ⟨tabT, tauT⟩ sigT hz m5A cos_all rep_all fus_all hN' hcard hm s hs
  have ht : prodAsc g (digitsOf 5 9 repIdx[k]!) = psi (g 0) (g 1) (bG g) (g 8) (dec (nthN repK k)) := by
    rw [digitsOf_dig9, prodAsc_eq_psi, V9.beq_eq (rep_dig k hk)]
  refine ⟨k, by rw [repIdx_size]; exact hk, by rw [ht]; exact hT, e, he0, he5, c, by rw [ht]; exact hc⟩

end CertificateChecks.KernelMonPcFive

end
