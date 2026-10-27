module

public import Certificates.Kernel.Misc.Perm.HS100.CliqueChecks
public import Certificates.Kernel.Misc.Perm.HS100.FiveGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCliqueData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Clique

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermAdj
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.FiveY
  CFSG.EvenSporadicStandard.HSStd.PumpHS
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of)

theorem nums' : K3.ng = 3 ∧ K3.N = 123200 ∧ K3.G 0 = HX.F 0 ∧ K3.G 1 = HX.F 1 ∧
    K3.G 2 = HX.F 15 ∧ K3.T K3.r0 = X3 := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  tauto

theorem hG : szOK 100 7 = true ∧ ∀ k < K3.ng, canonK 100 7 (mask 7) (100 * 7) (K3.G k) = true ∧
    canonK 100 7 (mask 7) (100 * 7) (K3.GI k) = true ∧
    permOK 100 7 (mask 7) (100 * 7) (K3.G k) (K3.GI k) = true :=
  CFSG.KC.ConjOrb.headK_spec K3.h

theorem canonG {k : ℕ} (hk : k < 3) : canonK 100 7 (mask 7) (100 * 7) (K3.G k) = true :=
  (hG.2 k (by rw [nums'.1]; exact hk)).1

theorem gens_get : ∀ k < hsGens.size, hsGens[k]! = unpack 100 7 (K3.G k) := by
  intro k hk
  have hk3 : k < 3 := hk
  interval_cases k
  · rw [nums'.2.2.1]; exact hs100Arr_eq 0 (by norm_num)
  · rw [nums'.2.2.2.1]; exact hs100Arr_eq 1 (by norm_num)
  · rw [nums'.2.2.2.2.1]; exact hs100Arr_eq 15 (by norm_num)

theorem cA : canonK 100 7 (mask 7) (100 * 7) (HX.F 0) = true := by
  have := canonG (k := 0) (by norm_num)
  rwa [nums'.2.2.1] at this

theorem cU : canonK 100 7 (mask 7) (100 * 7) (HX.F 15) = true := by
  have := canonG (k := 2) (by norm_num)
  rwa [nums'.2.2.2.2.1] at this

theorem cX3 : canonK 100 7 (mask 7) (100 * 7) X3 = true :=
  canonK_pcomp (canonK_pcomp cA cU) (canonK_pcomp cA cU)

theorem x3_eq : x3 = unpack 100 7 X3 := by
  rw [x3, hs100Arr_eq 0 (by norm_num), hs100Arr_eq 15 (by norm_num), compA_unpack cA cU,
    compA_unpack (canonK_pcomp cA cU) (canonK_pcomp cA cU)]
  rfl

theorem validG {k : ℕ} (hk : k < 3) : validA 100 hsGens[k]! = true := by
  rw [gens_get k hk]
  obtain ⟨h1, h2⟩ := invEqK_sound (hG.2 k (by rw [nums'.1]; exact hk)).2.2
  unfold validA
  rw [h1]
  exact h2

theorem x3_valid : validA 100 x3 = true := by
  have ra := rep_of_validA (validG (k := 0) (by norm_num))
  have ru := rep_of_validA (validG (k := 2) (by norm_num))
  exact CFSG.RankThree.Native.F2.validA_of_rep (rep_compA (rep_compA ra ru) (rep_compA ra ru))

theorem hcl : ∀ i < K3.N, CFSG.KC.ConjOrb.closPt 100 7 K3.ng K3.N K3.G K3.GI K3.T K3.E i = true :=
  fun i hi => K3.cl i (by rw [nums'.2.1] at hi; omega)

theorem cT : ∀ i < K3.N, canonK 100 7 (mask 7) (100 * 7) (K3.T i) = true :=
  fun i hi => (CFSG.KC.ConjOrb.closPt_spec (hcl i hi)).1

theorem keysOK3 : ∀ p ∈ hsKeys, p < 100 := by decide

theorem x3_mem : ∀ x, x ∈ x3Cert.pts ↔ ∃ i < K3.N, unpack 100 7 (K3.T i) = x := by
  have hN := nums'.2.1
  unfold x3Cert
  exact (CFSG.KC.ConjOrb.arrBfs_of_orb (ng := hsGens.size) (ngc := K3.ng) (fuel := 130000)
    (act := hsAct) (root := x3) (by rw [nums'.1]; rfl) gens_get (fun _ _ _ => rfl) K3.h hcl
    (fun i hi => K3.tr0 i (by rw [hN] at hi; omega)) (by rw [hN]; decide)
    (by rw [nums'.2.2.2.2.2, x3_eq]) x3_valid keysOK3 K3.k (by rw [hN]; norm_num)).2.1

theorem involA_eq {p : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) :
    involA (unpack 100 7 p) = invoK 100 7 p := by
  rw [involA, compA_unpack hp hp, hidA, eqA_F (canonK_pcomp hp hp) pidPP.1, eqA_F hp pidPP.1, invoK,
    Bool.and_comm]

theorem adjA_eq {p q : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true)
    (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    adjA (unpack 100 7 p) (unpack 100 7 q) = adjK 100 7 p q := by
  rw [adjA, compA_unpack hp hq, involA_eq (canonK_pcomp hp hq), adjK]

theorem fixedA_eq (p : ℕ) : fixedA (unpack 100 7 p) = CFSG.KC.PermAdj.fixedK 100 7 p := by
  rw [fixedA, CFSG.KC.PermAdj.fixedK, CFSG.KC.Misc.ArrEnum.anyNP_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq, Nat.beq_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [unpack_get' hi] at h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [unpack_get' hi]⟩

theorem mem_nbrL {b : Array ℕ} : b ∈ nbrL ↔ ∃ j < 261, unpack 100 7 (K3.T (NB j)) = b := by
  unfold nbrL
  rw [List.mem_filter, Array.mem_toList_iff, x3_mem]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, ha⟩
    rw [x3_eq, adjA_eq cX3 (cT i hi)] at ha
    have h := CFSG.KC.Misc.Clos.forall_of_chunks 1600 77 _ (fun c hc => nbrAll c hc) i
      (by rw [nums'.2.1] at hi; omega)
    unfold nbrPt at h
    cases e : (Nat.blt (INV i) 261 && Nat.beq (NB (INV i)) i)
    · rw [e] at h
      rw [ha] at h
      exact absurd h (by decide)
    · simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
      exact ⟨INV i, e.1, by rw [e.2]⟩
  · rintro ⟨j, hj, rfl⟩
    have h := allN_spec hNB j hj
    unfold nbPt at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    refine ⟨⟨_, h.1, rfl⟩, ?_⟩
    rw [x3_eq, adjA_eq cX3 (cT _ h.1)]
    exact h.2

theorem nbT {j : ℕ} (hj : j < 261) : NB j < K3.N := by
  have h := allN_spec hNB j hj
  unfold nbPt at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1

theorem cliqueAll : (nbrL.all fun b => fixedA (compA 100 x3 b) ||
    (let L := nbrL.filter fun c => adjA b c
     L.all fun c => L.all fun d => !adjA c d)) = true := by
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨j, hj, rfl⟩ := mem_nbrL.1 hb
  have hcb := cT _ (nbT hj)
  have h := allN_spec clique j hj
  unfold cliquePt at h
  rw [CFSG.KC.ConjOrb.strictB_eq, Bool.or_eq_true] at h
  rw [x3_eq, compA_unpack cX3 hcb, fixedA_eq, Bool.or_eq_true]
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    simp only [List.all_eq_true, List.mem_filter, Bool.not_eq_true']
    rintro c ⟨hc, hbc⟩ d ⟨hd, hbd⟩
    obtain ⟨j1, hj1, rfl⟩ := mem_nbrL.1 hc
    obtain ⟨j2, hj2, rfl⟩ := mem_nbrL.1 hd
    rw [adjA_eq hcb (cT _ (nbT hj1))] at hbc
    rw [adjA_eq hcb (cT _ (nbT hj2))] at hbd
    rw [adjA_eq (cT _ (nbT hj1)) (cT _ (nbT hj2))]
    have h1 := allN_spec h j1 hj1
    rw [hbc, Bool.not_true, Bool.false_or] at h1
    have h2 := allN_spec h1 j2 hj2
    rw [hbd, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at h2
    exact h2

theorem cliqueOK_true : cliqueOK = true := by
  unfold cliqueOK
  rw [Zassenhaus.HSFive.u0, CertificateChecks.KernelMisc.HS100.Five.tab_eq 0 (by norm_num),
    CertificateChecks.KernelMisc.HS100.Five.validF (by norm_num), cliqueAll]
  have h : ((List.range 100).all fun i =>
      (unpack 100 7 (CertificateChecks.KernelMisc.HS100.Five.FX.F 0))[i]! != i) = true := by
    decide +kernel
  rw [h]
  rfl

end CertificateChecks.KernelMisc.HS100.Clique

end
