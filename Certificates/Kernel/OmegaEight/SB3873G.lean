
module

public import Certificates.Kernel.OmegaEight.SB3873T
public import CFSG.Certificates.Kernel.O8.SBCenSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen

@[expose] def cenT (B : List ℕ) : ℕ := ((List.range 16).map fun s => B.getD s 0).sum

@[expose] noncomputable def chiF (r : ℕ) : Bool := decide (r < 131072) && (nfEK (r % 65536)).testBit 1

@[expose] def CenB (k m z : ℕ) (Q B : List ℕ) : Prop :=
  ∀ s < 16, (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    strictB Q.length fun n =>
      Nat.beq (cenBlk (extMulF 65536 mulK (rowF mulK nfEK nfAK W L) z) Q [64, 75] n (8192 * s))
        (B.getD s 0)) = true

@[expose] def CenC (k m z : ℕ) (Q B : List ℕ) : Prop :=
  (∀ s < 16, ((chunks 8 16 (t1Cls k m z)).getD s []).all (clsAt k m z) = true) ∧
    (t1Cls k m z).length ≤ 128 ∧
    (((t1Cls k m z).zip (t1Cls k m z).tail).all fun p => decide (p.1.1 < p.2.1)) = true ∧
    ((t1Cls k m z).map Prod.snd).sum = cenLane (cenT B) 0 ∧
    kRepsC (t1Cls k m z) 8 = Q ∧ 64 ∈ Q ∧ 75 ∈ Q

@[expose] def CenK (k m z : ℕ) (n5 : Bool) (Q B : List ℕ) : Prop :=
  ∀ p ∈ sMarked,
    killG (MK k m z) (IK k m z) t1Gens 131072 (fun r => cenLane (cenT B) (1 + Q.idxOf r)) Q
        (fun u => cenLane (cenT B) (1 + Q.length + [64, 75].idxOf u)) 8 chiF n5 p.1 p.2 = true ∧
      queriedG (MK k m z) (IK k m z) t1Gens (fun r => cenLane (cenT B) (1 + Q.idxOf r)) Q 8 chiF n5
        p.1 p.2 [64, 75] = true

theorem rowF_eq (k m x : ℕ) :
    rowF mulK nfEK nfAK (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) x = FK k m x := by
  unfold rowF FK WK LK
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, fld_eq, fld_eq]
  rfl

theorem MK_eqF (k m z : ℕ) :
    extMulF 65536 mulK (rowF mulK nfEK nfAK (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0)) z =
      MK k m z := by
  funext c d
  rw [extMulF_eq, MK]
  congr 1
  funext x
  exact rowF_eq k m x

theorem census_of {k m z : ℕ} {Q B : List ℕ} (h : CenB k m z Q B) :
    (kInv (MK k m z) 131072).length = cenLane (cenT B) 0 ∧
      (∀ i < Q.length,
        kCount (MK k m z) (kInv (MK k m z) 131072) (Q.getD i 0) = cenLane (cenT B) (1 + i)) ∧
      ∀ i < [64, 75].length, kCount (MK k m z) (kOrd4 (MK k m z) 131072) ([64, 75].getD i 0) =
        cenLane (cenT B) (1 + Q.length + i) := by
  refine census_counts (by norm_num) ?_
  rw [← MK_eqF]
  refine sum_cenBlk fun s hs => ?_
  have := h s hs
  rw [cen_strictB, cen_strictB, cen_strictB, cen_beq, decide_eq_true_eq] at this
  exact this

theorem t1KillC_of_cen {k m z : ℕ} {n5 : Bool} {Q B : List ℕ} (hA : PartA k m z) (hC : CenC k m z Q B)
    (hB : CenB k m z Q B) (hK : CenK k m z n5 Q B) : t1KillC k m z n5 = true := by
  obtain ⟨hconj, hw, hl, hcw, hcl, hz, hzχ⟩ := hA
  obtain ⟨hblk, hlen, hsort, hsum, hQ, h64, h75⟩ := hC
  obtain ⟨hinv, hcI, hcO⟩ := census_of hB
  have hconj' : conjOK k m z 0 65536 = true := by
    unfold conjOK
    rw [List.all_eq_true]
    intro y hy
    rw [List.mem_range'_1] at hy
    have hs : y / 8192 < 8 := by omega
    have := hconj _ hs
    unfold conjOK at this
    rw [List.all_eq_true] at this
    exact this y (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  have hcls : kClassOK (MK k m z) (IK k m z) t1Gens 131072 (t1Cls k m z) = true := by
    unfold kClassOK
    rw [Bool.and_eq_true, Bool.and_eq_true, hsort, hsum, ← hinv, beq_self_eq_true]
    refine ⟨⟨rfl, ?_⟩, rfl⟩
    rw [← chunks_flatten 8 16 (t1Cls k m z) hlen]
    refine all_blocks _ _ fun s hs => ?_
    rw [chunks_length] at hs
    exact hblk s hs
  have hchi : (fun r => (chiS 131072)[r]!) = chiF := by
    funext r
    rw [chiS_get]
    rfl
  refine t1KillC_of hw hl hconj' hz hzχ hcw hcl hcls fun p hp => ?_
  obtain ⟨hk, hq⟩ := hK p hp
  have ht : p.1 ∈ Q := by
    simp only [sMarked, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [h64, h75]
  change killAtCF _ _ _ _ _ _ _ _ _ _ _ _ = true
  rw [killAtCF_eq_killG, hchi, hQ]
  rw [killG_congr _ _ _ _ _ (fun r => cenLane (cenT B) (1 + Q.idxOf r)) _ _
    (fun u => cenLane (cenT B) (1 + Q.length + [64, 75].idxOf u)) _ _ _ _ _ [64, 75] ht
    (fun r hr => ?_) hq (fun u hu => ?_)]
  · exact hk
  · have hi := List.idxOf_lt_length_of_mem hr
    have := hcI _ hi
    rwa [List.getD_eq_getElem _ _ hi, List.getElem_idxOf hi] at this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact hcO 0 (by decide)
    · exact hcO 1 (by decide)

end CertificateChecks.KernelO8.SB3873

end
