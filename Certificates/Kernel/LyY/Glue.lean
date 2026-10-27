module

public import Certificates.Kernel.LyY.Chain
public import Certificates.Kernel.LyY.ScanAll
public import CFSG.Certificates.Kernel.LyY.ScanSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J2CoverSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Enum CFSG.KC.LyY
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.Sporadic.Recognition.LyonsSims

@[expose] noncomputable def yS : Array (Array Nat) :=
  Array.ofFn (n := 8) fun j => unpack 1080 11 (YC.S j.val)

theorem kBP : bAnd(Nat.beq (pg 11 (mask 11) YC.BP 0) 0, bAnd(Nat.beq (pg 11 (mask 11) YC.BP 1) 2,
    Nat.beq (pg 11 (mask 11) YC.BP 2) 6)) = true := by
  quickRfl

theorem binds : Binds 1080 11 YC.S 8 3 YC.BP yS yBase := by
  have h := kBP
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [yS], fun j hj => ?_, rfl, fun t ht => ?_⟩
  · rw [getElem!_pos yS j (by simp [yS]; omega)]
    simp [yS]
  · interval_cases t
    · rw [Nat.eq_of_beq_eq_true h0]; rfl
    · rw [Nat.eq_of_beq_eq_true h1]; rfl
    · rw [Nat.eq_of_beq_eq_true h2]; rfl

theorem ties : YC.S 0 = CertificateChecks.KernelLyTr.UH.F 0 ∧
    YC.S 1 = CertificateChecks.KernelLyTr.UH.F 3 ∧ rcnt (YC.LR 0) = 1080 ∧
    rcnt (YC.LR 1) = 54 ∧ rcnt (YC.LR 2) = 6 ∧
    allN 8 (fun j => permOK 1080 11 (mask 11) (1080 * 11) (YC.S j) (YC.SI j)) = true := by
  have h := k_ties
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, h5⟩

theorem chainYC : ChainOK3 1080 11 8 2 YC.BP 18 60 YC.S YC.SI YC.LR YC.TR YC.TRI yD yS yBase :=
  ⟨binds, YC.head, YC.hl, by norm_num, YC.hs, ties.2.2.2.2.2⟩

theorem k20 : rcnt (YC.LR 0) * rcnt (YC.LR 1) * rcnt (YC.LR 2) < 2 ^ 20 := by
  rw [ties.2.2.1, ties.2.2.2.1, ties.2.2.2.2.1]
  norm_num

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem sumF_congr {f g : Nat → Nat} : ∀ m, (∀ a < m, f a = g a) → sumF m f = sumF m g
  | 0, _ => rfl
  | m + 1, h => by
    have e : ∀ r : Nat → Nat, sumF (m + 1) r = sumF m r + r m := fun r => by
      change strictN (sumF m r) (fun s' => Nat.add s' (r m)) = _
      rw [strictN_eq']
      rfl
    rw [e, e, sumF_congr m fun a ha => h a (by omega), h m (by omega)]

theorem sumY : sumF (rcnt (YC.LR 0)) (blkY 1080 11 YC.LR YC.TR YC.TRI YC.BP (YC.S 0) (YC.SI 0)
    Ly1080.autRelators Ly1080.autWitnesses) = sumF 1080 (lget E) := by
  rw [ties.2.2.1]
  exact sumF_congr 1080 fun a ha => Nat.eq_of_beq_eq_true (fE_all a ha)

theorem kX : canonK 1080 11 (mask 11) (1080 * 11) (YC.S 0) = true ∧
    siftK 1080 11 (mask 11) (1080 * 11) (pidn 1080 11) YC.LR YC.TRI YC.BP 3 0 (YC.S 0) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem lettersAut : lettersTwo Ly1080.autRelators ∧ lettersTwo Ly1080.autWitnesses := by
  unfold lettersTwo
  decide

theorem counts :
    (filterProducts 1080 (ordTest 1080 12) (chainTables 1080 yS yBase) (idT 1080) []).countP
        (relTestW 1080 Ly1080.autRelators Ly1080.autWitnesses
          (arrTable 1080 (unpack 1080 11 (YC.S 0)))) = 288 ∧
    (filterProducts 1080 (ordTest 1080 2) (chainTables 1080 yS yBase) (idT 1080) []).length =
      2511 := by
  have h := blkY_sound chainYC k20 kX (allN_spec ties.2.2.2.2.2 0 (by norm_num))
    lettersAut.1 lettersAut.2
  have ht := k_tot
  simp only [bAnd_iff] at ht
  rw [sumY, Nat.eq_of_beq_eq_true ht.1, Nat.eq_of_beq_eq_true ht.2] at h
  exact h

end CertificateChecks.KernelLyY

end
