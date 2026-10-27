module

public import CFSG.Certificates.Kernel.MonsterPcFive.Bridge
import Certificates.Kernel.MonsterPcFive.Tab
import Certificates.Kernel.MonsterPcFive.E3

public section

namespace CertificateChecks.KernelMonPcFive

open CFSG.KC.MonPcFive CFSG.KC.MonPcFiveD
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus (prodAsc)
open _root_.Timmesfeld.PcFive (pw cw repIdx)
open _root_.Timmesfeld.PcReg (digitsOf)

@[expose] def dig9 (i : ℕ) : Array ℕ :=
  (List.foldl (fun (b : Array ℕ × ℕ) a => (b.fst.setIfInBounds (8 - a) (b.snd % 5), b.snd / 5))
    (Array.replicate 9 0, i) (List.range' 0 9)).fst

theorem digitsOf_dig9 (i : ℕ) : digitsOf 5 9 i = dig9 i := by
  unfold digitsOf dig9
  simp [Id.run]
  generalize (List.foldl (fun (b : Array ℕ × ℕ) a =>
    (b.fst.setIfInBounds (8 - a) (b.snd % 5), b.snd / 5)) (Array.replicate 9 0, i)
    (List.range' 0 9)).fst = A
  rfl

theorem rep_dig : ∀ k < 31, (vecV (dig9 repIdx[k]!)).beq (dec (nthN repK k)) = true := by
  decide +kernel

theorem repIdx_size : repIdx.size = 31 := by decide +kernel

theorem e3_chunk {lo n : ℕ} (h : e3OK lo n = true) {k : ℕ} (h1 : lo ≤ k) (h2 : k < lo + n) :
    tripV (dec (nthN repK k)) (dec (nthN e3A k)) (dec (nthN e3B k)) = true := by
  unfold e3OK at h
  have e := allBelow_spec h (k - lo) (by omega)
  simp only [Nat.add_sub_cancel' h1] at e
  exact e

theorem e3_all {k : ℕ} (hk : k < 31) :
    tripV (dec (nthN repK k)) (dec (nthN e3A k)) (dec (nthN e3B k)) = true := by
  rcases Nat.lt_or_ge k 8 with h | h
  · exact e3_chunk e3_0 (by omega) (by omega)
  rcases Nat.lt_or_ge k 16 with h' | h'
  · exact e3_chunk e3_1 h (by omega)
  rcases Nat.lt_or_ge k 24 with h'' | h''
  · exact e3_chunk e3_2 h' (by omega)
  · exact e3_chunk e3_3 h'' (by omega)

theorem fiveE3Witness {G : Type} [Group G] [Finite G] (g : Fin 9 → G)
    (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
    (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!)
    (hz : g 8 ≠ 1) :
    ∀ k < repIdx.size, ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 3 ∧
      prodAsc g (digitsOf 5 9 repIdx[k]!) ∈ E := by
  intro k hk
  rw [repIdx_size] at hk
  have H := pcHyp_of_rel hpow hcomm
  obtain ⟨hTA, hTB, hAB, hT, hA, hB, hind⟩ :=
    tripV_sound H ⟨tabT, tauT⟩ sigT hz (dec_red _) (dec_red _) (dec_red _) (e3_all hk)
  obtain ⟨E, hE, hc, hmem⟩ := elemAbelian_of_triple hTA hTB hAB hT hA hB hind
  refine ⟨E, hE, hc, ?_⟩
  rw [digitsOf_dig9, prodAsc_eq_psi, V9.beq_eq (rep_dig k hk)]
  exact hmem

end CertificateChecks.KernelMonPcFive

end
