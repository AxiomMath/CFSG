module

public import Certificates.Kernel.Misc.Perm.HS100.NbrChecks
public import Certificates.Kernel.Misc.Perm.HS100.S0Glue
public import Certificates.Kernel.Misc.Perm.HS100.CliqueGlue

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Nbr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermAdj
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.FiveY
  CFSG.EvenSporadicStandard.HSStd.PumpHS
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP)

theorem XN_eq : XN = Clique.X3 := rfl

theorem cXNI : canonK 100 7 (mask 7) (100 * 7) XNI = true := by
  rw [XNI, XN_eq]
  exact canonK_pcomp Clique.cX3 Clique.cX3

theorem cSRC {i : ℕ} (hi : i < 21175) : canonK 100 7 (mask 7) (100 * 7) (SRC i) = true := by
  unfold SRC
  cases e : Nat.blt i 5775
  · have : ¬ i < 5775 := fun h => by
      have h' : Nat.blt i 5775 = true := by simpa only [Nat.blt_eq] using h
      rw [h'] at e
      cases e
    exact S0.uT_canon (by omega)
  · exact S0.zT_canon (by simpa only [Nat.blt_eq] using e)

theorem cTT {i : ℕ} (hi : i < 21175) : canonK 100 7 (mask 7) (100 * 7) (TT i) = true :=
  canonK_pcomp cXNI (cSRC hi)

theorem src_mem (x : Array ℕ) : x ∈ invPtsL ↔ ∃ i < 21175, unpack 100 7 (SRC i) = x := by
  unfold invPtsL
  rw [List.mem_append, Array.mem_toList_iff, Array.mem_toList_iff, S0.zOrbit_mem, S0.uOrbit_mem]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · refine ⟨i, by omega, ?_⟩
      have e : Nat.blt i 5775 = true := by simpa only [Nat.blt_eq] using hi
      rw [SRC, e]
    · refine ⟨5775 + i, by omega, ?_⟩
      have e : Nat.blt (5775 + i) 5775 = false := by
        cases h : Nat.blt (5775 + i) 5775
        · rfl
        · have : 5775 + i < 5775 := by simpa only [Nat.blt_eq] using h
          omega
      rw [SRC, e, Nat.add_sub_cancel_left]
  · rintro ⟨i, hi, rfl⟩
    unfold SRC
    cases e : Nat.blt i 5775
    · have : ¬ i < 5775 := fun h => by
        have h' : Nat.blt i 5775 = true := by simpa only [Nat.blt_eq] using h
        rw [h'] at e
        cases e
      exact Or.inr ⟨i - 5775, by omega, rfl⟩
    · exact Or.inl ⟨i, by simpa only [Nat.blt_eq] using e, rfl⟩

theorem x3i_eq {i : ℕ} (hi : i < 21175) :
    compA 100 (compA 100 x3 x3) (unpack 100 7 (SRC i)) = unpack 100 7 (TT i) := by
  rw [Clique.x3_eq, compA_unpack Clique.cX3 Clique.cX3,
    compA_unpack (canonK_pcomp Clique.cX3 Clique.cX3) (cSRC hi), TT, XNI, XN_eq]

theorem cube_eq {p : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) :
    eqA 100 (compA 100 (unpack 100 7 p) (compA 100 (unpack 100 7 p) (unpack 100 7 p))) (idA 100) =
      cube3K p := by
  rw [compA_unpack hp hp, compA_unpack hp (canonK_pcomp hp hp), hidA,
    eqA_F (canonK_pcomp hp (canonK_pcomp hp hp)) pidPP.1]
  rfl

theorem nbF {j : ℕ} (hj : j < 261) :
    NBI j < 21175 ∧ NLP j = TT (NBI j) ∧ cube3K (NLP j) = true := by
  have h := allN_spec hNBI j hj
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cNLP {j : ℕ} (hj : j < 261) : canonK 100 7 (mask 7) (100 * 7) (NLP j) = true := by
  rw [(nbF hj).2.1]
  exact cTT (nbF hj).1

theorem nbr_mem {b : Array ℕ} : b ∈ nbrL ↔ ∃ j < 261, unpack 100 7 (NLP j) = b := by
  unfold nbrL
  rw [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hc⟩
    obtain ⟨i, hi, rfl⟩ := (src_mem u).1 hu
    rw [x3i_eq hi] at hc ⊢
    rw [cube_eq (cTT hi)] at hc
    have h := CFSG.KC.Misc.Clos.forall_of_chunks 1925 11 _ (fun c hc => selAll c hc) i
      (by omega)
    unfold selPt at h
    cases e : (Nat.blt (INVI i) 261 && Nat.beq (NBI (INVI i)) i)
    · rw [e] at h
      change cube3K (TT i) = true at hc
      rw [hc] at h
      exact absurd h (by decide)
    · simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
      refine ⟨INVI i, e.1, ?_⟩
      rw [(nbF e.1).2.1, e.2]
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨h1, h2, h3⟩ := nbF hj
    refine ⟨⟨unpack 100 7 (SRC (NBI j)), (src_mem _).2 ⟨_, h1, rfl⟩, ?_⟩, ?_⟩
    · rw [x3i_eq h1, h2]
    · rw [cube_eq (cNLP hj)]
      exact h3

theorem cliqueAllN : (nbrL.all fun b => fixedA (compA 100 x3 b) ||
    (let L := nbrL.filter fun c => adjA b c
     L.all fun c => L.all fun d => !adjA c d)) = true := by
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨j, hj, rfl⟩ := nbr_mem.1 hb
  have hcb := cNLP hj
  have h := allN_spec cliqueI j hj
  unfold cliquePt at h
  rw [CFSG.KC.ConjOrb.strictB_eq, Bool.or_eq_true] at h
  rw [Clique.x3_eq, compA_unpack Clique.cX3 hcb, Clique.fixedA_eq, Bool.or_eq_true, ← XN_eq]
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    simp only [List.all_eq_true, List.mem_filter, Bool.not_eq_true']
    rintro c ⟨hc, hbc⟩ d ⟨hd, hbd⟩
    obtain ⟨j1, hj1, rfl⟩ := nbr_mem.1 hc
    obtain ⟨j2, hj2, rfl⟩ := nbr_mem.1 hd
    rw [Clique.adjA_eq hcb (cNLP hj1)] at hbc
    rw [Clique.adjA_eq hcb (cNLP hj2)] at hbd
    rw [Clique.adjA_eq (cNLP hj1) (cNLP hj2)]
    have h1 := allN_spec h j1 hj1
    rw [hbc, Bool.not_true, Bool.false_or] at h1
    have h2 := allN_spec h1 j2 hj2
    rw [hbd, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at h2
    exact h2

theorem cliqueOK_true : cliqueOK = true := by
  unfold cliqueOK
  rw [Zassenhaus.HSFive.u0, CertificateChecks.KernelMisc.HS100.Five.tab_eq 0 (by norm_num),
    CertificateChecks.KernelMisc.HS100.Five.validF (by norm_num), cliqueAllN]
  have h : ((List.range 100).all fun i =>
      (unpack 100 7 (CertificateChecks.KernelMisc.HS100.Five.FX.F 0))[i]! != i) = true := by
    decide +kernel
  rw [h]
  rfl

end CertificateChecks.KernelMisc.HS100.Nbr

end
