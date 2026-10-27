module

public import Certificates.Kernel.PlusFrame.PinChecks
public import Certificates.Kernel.PlusFrame.Facts
public import Certificates.Kernel.PlusFactors.Facts
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
import all Init.Data.Nat.Fold
import CFSG.Certificates.Kernel.Spor.RawOrbEval

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPlusFr

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.PlusFrame CFSG.KC.Enum
  CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Monster.B.Co2
open CertificateChecks.KernelPlusF
local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem prod_ok : frameProdCheck () = true := by decide +kernel

theorem valid_ok : derivValidCheck () = true := by decide +kernel

theorem numsF : PT.ng = 3 ∧ PT.N = 32 ∧ PC0.ng = 3 ∧ PC0.N = 8 ∧ PC1.ng = 3 ∧ PC1.N = 8 ∧
    PC2.ng = 3 ∧ PC2.N = 8 ∧ PC3.ng = 3 ∧ PC3.N = 8 := by
  have h := kNumsF
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  tauto

theorem bindT : t0Gens.size = 3 ∧ ∀ k < 3, t0Gens[k]! = unpack 60 6 (PT.G k) :=
  binds_of_check kBindT

theorem permT : ∀ k < PT.ng,
    permOK 60 6 (mask 6) (60 * 6) (PT.G k) (pinvS 60 6 (mask 6) (PT.G k)) = true := by
  intro k hk
  rw [numsF.1] at hk
  exact AI.1 (and_of (and_of (and_of (and_of kPermF).1).1).1).1 k hk

theorem ppT : ∀ i < PT.N, PP 60 6 (PT.T i) := PP_pts PT.ok permT

theorem gT {k : ℕ} (hk : k < 3) : PP 60 6 (PT.G k) :=
  PP_gen PT.ok permT k (by rw [numsF.1]; exact hk)

theorem pinT : (t0Cert ()).pts = Array.ofFn (n := PT.N) fun i => unpack 60 6 (PT.T i.val) :=
  enumBfs_pts_base (by rw [bindT.1, numsF.1])
    (fun k hk => bindT.2 k (by rw [numsF.1] at hk; exact hk)) PT.ok keysOK kKT
    (by rw [numsF.2.1]; norm_num)

theorem t0_ok : t0Check (t0Cert ()) = true := by
  have he : enumOK 60 t0Gens plusBase (t0Cert ()) = true :=
    enumOK_of_bfsK_base (by rw [bindT.1, numsF.1])
      (fun k hk => bindT.2 k (by rw [numsF.1] at hk; exact hk)) permT PT.ok keysOK kKT
      (by rw [numsF.2.1]; norm_num)
  unfold t0Check
  rw [he, pinT, Array.size_ofFn, numsF.2.1]
  rfl

theorem sub_ok : t0SubCheck (plusEnum ()) = true := by
  unfold t0SubCheck
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 3 := by rw [List.mem_range, bindT.1] at hk; exact hk
  rw [bindT.2 k hk', any_pin pinE ppE (gT hk')]
  exact AI.1 kSub k hk'

theorem mem_ok : frameMemCheck (t0Cert ()) = true := by
  unfold frameMemCheck
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  rw [bindE.2 k hk', any_pin pinT ppT (gE hk'), ← CFSG.KC.PlusFrameK.isFr_eq]
  exact AI.1 kMemF k hk'

theorem card_of {gs : Array (Array ℕ)} {ng N : ℕ} {G T E S : ℕ → ℕ} {SK : List ℕ}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack 60 6 (G k))
    (hp : ∀ k < ng, permOK 60 6 (mask 6) (60 * 6) (G k) (pinvS 60 6 (mask 6) (G k)) = true)
    (hk : bfsK 60 6 ng G N T E S = true) (hK : keysSK 60 6 plusBase N T SK = true) (hN : N = 8) :
    (enumOK 60 gs plusBase (enumBfs 60 gs plusBase 16) &&
      ((enumBfs 60 gs plusBase 16).pts.size == 8)) = true := by
  rw [enumOK_of_bfsK_base hs hg hp hk keysOK hK (by omega),
    enumBfs_pts_base hs hg hk keysOK hK (by omega), Array.size_ofFn, hN]
  rfl

theorem perm_of {G : ℕ → ℕ} {ng : ℕ} (hng : ng = 3) (h : allN 3 (gOK G) = true) :
    ∀ k < ng, permOK 60 6 (mask 6) (60 * 6) (G k) (pinvS 60 6 (mask 6) (G k)) = true := by
  intro k hk
  rw [hng] at hk
  exact AI.1 h k hk

theorem card_ok : cardCheck () = true := by
  unfold cardCheck
  rw [List.all_eq_true]
  intro i _
  have b0 := binds_of_check kBindC0
  have b1 := binds_of_check kBindC1
  have b2 := binds_of_check kBindC2
  have b3 := binds_of_check kBindC3
  have p := kPermF
  simp only [Bool.and_eq_true] at p
  have c0 := card_of (b0.1.trans numsF.2.2.1.symm)
    (fun k hk => b0.2 k (by rw [numsF.2.2.1] at hk; exact hk))
    (perm_of numsF.2.2.1 p.1.1.1.2) PC0.ok kKC0 numsF.2.2.2.1
  have c1 := card_of (b1.1.trans numsF.2.2.2.2.1.symm)
    (fun k hk => b1.2 k (by rw [numsF.2.2.2.2.1] at hk; exact hk))
    (perm_of numsF.2.2.2.2.1 p.1.1.2) PC1.ok kKC1 numsF.2.2.2.2.2.1
  have c2 := card_of (b2.1.trans numsF.2.2.2.2.2.2.1.symm)
    (fun k hk => b2.2 k (by rw [numsF.2.2.2.2.2.2.1] at hk; exact hk))
    (perm_of numsF.2.2.2.2.2.2.1 p.1.2) PC2.ok kKC2 numsF.2.2.2.2.2.2.2.1
  have c3 := card_of (b3.1.trans numsF.2.2.2.2.2.2.2.2.1.symm)
    (fun k hk => b3.2 k (by rw [numsF.2.2.2.2.2.2.2.2.1] at hk; exact hk))
    (perm_of numsF.2.2.2.2.2.2.2.2.1 p.2) PC3.ok kKC3 numsF.2.2.2.2.2.2.2.2.2
  fin_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3

theorem fr_eq (i : Fin 4) : frameArr[(i : ℕ)]! = frV i := by
  fin_cases i <;> rfl

theorem fr_lt (i : ℕ) : frV i < 60 := by
  unfold frV
  cases Nat.beq i 0 <;> cases Nat.beq i 1 <;> cases Nat.beq i 2 <;> decide

theorem ofNat_eq {i : ℕ} (hi : i < 4) : Fin.ofNat 4 i = ⟨i, hi⟩ :=
  Fin.ext (by rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hi)

theorem mapsFrame_eq (x : ℕ) : mapsFrame (unpack 60 6 x) = mapsP x := by
  rw [Bool.eq_iff_iff, mapsP, AI, mapsFrame, List.all_eq_true]
  constructor
  · intro h i hi
    have h1 := h ⟨i, hi⟩ (List.mem_finRange _)
    rw [List.any_eq_true] at h1
    obtain ⟨j, _, hj⟩ := h1
    rw [anyN_eq, List.any_eq_true]
    refine ⟨j, List.mem_range.2 j.2, ?_⟩
    rw [fr_eq, fr_eq, unpack_get' (fr_lt _), beq_iff_eq] at hj
    rw [Nat.beq_eq]
    exact hj
  · intro h i _
    have h1 := h i i.2
    rw [anyN_eq, List.any_eq_true] at h1
    obtain ⟨j, hj, e⟩ := h1
    rw [List.any_eq_true]
    refine ⟨⟨j, List.mem_range.1 hj⟩, List.mem_finRange _, ?_⟩
    rw [fr_eq, fr_eq, unpack_get' (fr_lt _), beq_iff_eq]
    rw [Nat.beq_eq] at e
    exact e

theorem matchesPerm_eq (x : ℕ) (σ : Fin 4 → Fin 4) :
    matchesPerm (unpack 60 6 x) σ = matchP x σ := by
  rw [Bool.eq_iff_iff, matchP, AI, matchesPerm, List.all_eq_true]
  constructor
  · intro h i hi
    have h1 := h ⟨i, hi⟩ (List.mem_finRange _)
    rw [fr_eq, fr_eq, unpack_get' (fr_lt _), beq_iff_eq] at h1
    rw [Nat.beq_eq, ofNat_eq hi]
    exact h1
  · intro h i _
    have h1 := h i i.2
    rw [Nat.beq_eq, ofNat_eq i.2] at h1
    rw [fr_eq, fr_eq, unpack_get' (fr_lt _), beq_iff_eq]
    exact h1

theorem even_ok : evenCheck (plusEnum ()) = true := by
  unfold evenCheck
  rw [allLt_iff]
  intro k hk
  rw [pinE, Array.size_ofFn] at hk
  simp only []
  rw [pinE, ofFn_get hk, mapsFrame_eq]
  have e : (oddPerms.all fun σ => !(matchesPerm (unpack 60 6 (PE.T k)) σ)) =
      (oddPerms.all fun σ => !(matchP (PE.T k) σ)) := by
    simp only [matchesPerm_eq]
  rw [e]
  exact AI.1 kEven k hk

theorem alt_ok : alternatingCheck (plusEnum ()) = true := by
  unfold alternatingCheck
  rw [List.all_eq_true]
  intro σ hσ
  have h := List.all_eq_true.1 kAlt σ hσ
  rw [anyN_eq, List.any_eq_true] at h
  obtain ⟨k, hk, hm⟩ := h
  rw [List.any_eq_true]
  refine ⟨unpack 60 6 (PE.T k), ?_, by rw [matchesPerm_eq]; exact hm⟩
  rw [pinE, pts_toList (fun i => unpack 60 6 (PE.T i))]
  exact List.mem_map_of_mem hk

theorem frame : frameCheck () = true := by
  simp only [frameCheck, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨t0_ok, sub_ok⟩, mem_ok⟩, prod_ok⟩, card_ok⟩, even_ok⟩, alt_ok⟩, aut⟩, valid_ok⟩

end CertificateChecks.KernelPlusFr
