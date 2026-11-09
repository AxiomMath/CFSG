
module

public import Certificates.Kernel.Misc.Perm.J2C3B
public import Certificates.Kernel.Misc.Perm.J2C3D
import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Misc.Perm.HexSplitCmd
import CFSG.Certificates.Kernel.Misc.ArrEnumOps
import CFSG.Certificates.Kernel.Spor.PinvSPcomp
import Certificates.Kernel.Misc.Perm.J2C3CData
meta import Certificates.Kernel.Misc.Perm.J2C3CData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.J2C3.NZP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZPHex
#kmisc_hexflat_split CertificateChecks.KernelMisc.J2C3.NZP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZPHex
  3 315 9 2160 100000
#ks_chars CertificateChecks.KernelMisc.J2C3.NZE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZEHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZEHex
  3 3 12 2160
#ks_chars CertificateChecks.KernelMisc.J2C3.NZR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZRHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZRHex
  3 2160 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.NZL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZLHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZLHex
  3 2160 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.NZS CertificateChecks.KernelMisc.J2C3.nzSortHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZS CertificateChecks.KernelMisc.J2C3.nzSortHex
  3 2160 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.NZI CertificateChecks.KernelMisc.J2C3.nzInvHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZI CertificateChecks.KernelMisc.J2C3.nzInvHex
  3 2160 12 1

public section

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.KC.Misc.SetCodes
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.Misc.Clos (allN_iff allR forall_of_chunks)

theorem nz : Bound cNZ 2160 3 NZP.F NZE.F NZR.F NZL.F := by
  unfold cNZ cNZLit
  exact cert_facts NZP.eq NZP.all NZE.eq NZE.all NZR.eq NZR.all NZL.eq NZL.all

@[expose] noncomputable def GNZ (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (GC 0)
    (fun j _ => Nat.rec (motive := fun _ => ℕ) (GC 1) (fun _ _ => G0) j) k

theorem gnz_size : gensNZArr.size = 3 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem hgnz (k : ℕ) (hk : k < 3) : gensNZArr[k]! = unpack 315 9 (GNZ k) := by
  have hs : gensCzArr.size = 2 := gcz_size
  unfold gensNZArr
  interval_cases k
  · rw [getElem!_pos _ 0 (by simp [hs]), Array.getElem_push_lt (by omega), ← getElem!_pos]
    exact hgc 0 (by norm_num)
  · rw [getElem!_pos _ 1 (by simp [hs]), Array.getElem_push_lt (by omega), ← getElem!_pos]
    exact hgc 1 (by norm_num)
  · have e : (gensCzArr.push g0Arr)[2]! = g0Arr := by
      rw [getElem!_pos _ 2 (by simp [hs])]
      simp [Array.getElem_push, hs]
    rw [e]
    exact hg0

@[expose] noncomputable def npK (p : ℕ) : Bool :=
  !(memK 27 P3P.F (pcomp 315 9 (mask 9) p (pcomp 315 9 (mask 9) X (pinvS 315 9 (mask 9) p))) &&
      memK 27 P3P.F (pcomp 315 9 (mask 9) p (pcomp 315 9 (mask 9) Y (pinvS 315 9 (mask 9) p))))
    || memK 216 NPP.F p

@[expose] noncomputable def npIK (k : ℕ) : Bool :=
  Nat.blt (VF NZI.F k) 2160 &&
    Nat.beq (pcomp 315 9 (mask 9) (NZP.F k) (NZP.F (VF NZI.F k))) (pidn 315 9) &&
    (!(memK 27 P3P.F (pcomp 315 9 (mask 9) (NZP.F k)
          (pcomp 315 9 (mask 9) X (NZP.F (VF NZI.F k)))) &&
        memK 27 P3P.F (pcomp 315 9 (mask 9) (NZP.F k)
          (pcomp 315 9 (mask 9) Y (NZP.F (VF NZI.F k)))))
      || memK 216 NPP.F (NZP.F k))

@[expose] noncomputable def ptNZK (i : ℕ) : Bool :=
  CFSG.KC.LQT.P.allN 3 (fun k => Nat.blt (EF NZE.F i k) 2160 &&
      Nat.beq (NZP.F (EF NZE.F i k)) (pcomp 315 9 (mask 9) (GNZ k) (NZP.F i))) &&
    (i == 0 || (Nat.blt (VF NZR.F i) i && Nat.blt (VF NZL.F i) 3 &&
      Nat.beq (EF NZE.F (VF NZR.F i) (VF NZL.F i)) i))

theorem nz0 : NZP.F 0 = pidn 315 9 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem pGNZ (k : ℕ) (hk : k < 3) : permB 315 9 (GNZ k) = true := by
  interval_cases k <;> quickRfl

theorem treeNZ (h : ∀ j < 2160, ptNZK j = true) {i : ℕ} (hi : i < 2160)
    (hp : VF NZR.F i < i ∧ VF NZL.F i < 3) (he : EF NZE.F (VF NZR.F i) (VF NZL.F i) = i) :
    NZP.F i = pcomp 315 9 (mask 9) (GNZ (VF NZL.F i)) (NZP.F (VF NZR.F i)) := by
  have hq := h _ (by omega : VF NZR.F i < 2160)
  simp only [ptNZK, Bool.and_eq_true] at hq
  have hE := (allN_iff _ _).1 hq.1 _ hp.2
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hE
  rw [he] at hE
  exact hE.2

theorem permB_NZ (h : ∀ j < 2160, ptNZK j = true) :
    ∀ i < 2160, permB 315 9 (NZP.F i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hi' := h i hi
    simp only [ptNZK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq,
      Nat.beq_eq] at hi'
    rcases hi'.2 with rfl | ⟨hp, he⟩
    · rw [nz0]
      exact pI
    · rw [treeNZ h hi hp he]
      exact permB_pcomp hw (pGNZ _ hp.2) (ih _ hp.1 (by omega))

theorem pointK_of_ptNZK (h : ∀ j < 2160, ptNZK j = true) (i : ℕ) (hi : i < 2160) :
    pointK 315 9 3 2160 GNZ NZP.F (EF NZE.F) (VF NZR.F) (VF NZL.F) i = true := by
  have hi' := h i hi
  simp only [ptNZK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq] at hi'
  obtain ⟨h2, h3⟩ := hi'
  simp only [pointK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq]
  exact ⟨⟨permB_NZ h i hi, h2⟩, h3.imp id fun hp => ⟨hp.1, treeNZ h hi hp.1 hp.2⟩⟩

@[expose] noncomputable def tenK (p : ℕ) : Bool :=
  permutesK 10 9 9 S10 p &&
    (!fixesK 10 9 9 S10 p || (Nat.beq p I || Nat.beq p Z || Nat.beq p (cm Z Z)))

@[expose] noncomputable def ptNZC : ℕ → Bool := chunkK 90 ptNZK

@[expose] noncomputable def kyNZK (q : ℕ) : Bool :=
  Nat.blt (VF NZS.F q) 2160 &&
    (!Nat.blt (Nat.succ q) 2160 ||
      Nat.blt (keyK 315 9 keyPts (NZP.F (VF NZS.F q)))
        (keyK 315 9 keyPts (NZP.F (VF NZS.F (Nat.succ q)))))

theorem inj_of_sortNZ {N : ℕ} {σ f : ℕ → ℕ} (hs : ∀ i < N, σ i < N)
    (hlt : ∀ i, i + 1 < N → f (σ i) < f (σ (i + 1))) :
    ∀ a < N, ∀ b < N, f a = f b → a = b := by
  have mono : ∀ i j, i < j → j < N → f (σ i) < f (σ j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) (hlt j hj)
      · subst h
        exact hlt i hj
  have sinj : ∀ i < N, ∀ j < N, f (σ i) = f (σ j) → i = j := by
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · exact absurd e (ne_of_lt (mono i j h hj))
    · exact h
    · exact absurd e (ne_of_gt (mono j i h hi))
  have himg : (Finset.range N).image σ = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hs i (Finset.mem_range.1 hi))
    · rw [Finset.card_image_of_injOn]
      intro i hi j hj e
      exact sinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) (by rw [e])
  have surj : ∀ a < N, ∃ i < N, σ i = a := by
    intro a ha
    have : a ∈ (Finset.range N).image σ := by
      rw [himg]
      exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := surj a ha
  obtain ⟨j, hj, rfl⟩ := surj b hb
  rw [sinj i hi j hj e]

@[expose] noncomputable def kyNZC : ℕ → Bool := chunkK 90 kyNZK

@[expose] noncomputable def npNZC : ℕ → Bool := chunkK 90 npIK

@[expose] noncomputable def tenNZC : ℕ → Bool := chunkK 90 fun k => tenK (NZP.F k)

end CertificateChecks.KernelMisc.J2C3

#kc_each CertificateChecks.KernelMisc.J2C3.ptNZC 0 24
#kc_each CertificateChecks.KernelMisc.J2C3.kyNZC 0 24
#kc_each CertificateChecks.KernelMisc.J2C3.npNZC 0 24
#kc_each CertificateChecks.KernelMisc.J2C3.tenNZC 0 24

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.KC.Misc.SetCodes
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Co2 (allLt_iff)

#kc_forall_chunks ptNZS (fun c => ptNZC c = true) 24 CertificateChecks.KernelMisc.J2C3.ptNZC 1
#kc_forall_chunks kyNZS (fun c => kyNZC c = true) 24 CertificateChecks.KernelMisc.J2C3.kyNZC 1
#kc_forall_chunks npNZS (fun c => npNZC c = true) 24 CertificateChecks.KernelMisc.J2C3.npNZC 1
#kc_forall_chunks tenNZS (fun c => tenNZC c = true) 24 CertificateChecks.KernelMisc.J2C3.tenNZC 1

theorem ptNZ_All : ∀ i < 2160,
    (pointK 315 9 3 2160 GNZ NZP.F (EF NZE.F) (VF NZR.F) (VF NZL.F)) i = true :=
  pointK_of_ptNZK (all_of_chunks 90 24 ptNZS)

theorem kyNZ_All : ∀ i < 2160, ∀ j < i,
    keyK 315 9 keyPts (NZP.F i) ≠ keyK 315 9 keyPts (NZP.F j) := by
  have h : ∀ q < 2160, kyNZK q = true := all_of_chunks 90 24 kyNZS
  have hinj := inj_of_sortNZ (N := 2160) (σ := VF NZS.F)
    (f := fun i => keyK 315 9 keyPts (NZP.F i))
    (fun i hi => by
      have h1 := h i hi
      unfold kyNZK at h1
      rw [Bool.and_eq_true] at h1
      simpa only [Nat.blt_eq] using h1.1)
    (fun i hi => by
      have h1 := h i (by omega)
      unfold kyNZK at h1
      rw [Bool.and_eq_true] at h1
      have hb : Nat.blt (Nat.succ i) 2160 = true := by simpa only [Nat.blt_eq] using hi
      simpa only [hb, Bool.not_true, Bool.false_or, Nat.blt_eq] using h1.2)
  intro i hi j hj e
  exact absurd (hinj i hi j (by omega) e) (by omega)

theorem tenNZ_All : ∀ i < 2160, (fun k => tenK (NZP.F k)) i = true := all_of_chunks 90 24 tenNZS

theorem nzp (k : ℕ) (hk : k < 2160) : permB 315 9 (NZP.F k) = true := by
  have h := ptNZ_All k hk
  simp only [pointK, Bool.and_eq_true] at h
  exact h.1.1

theorem npNZ_All : ∀ i < 2160, (fun k => npK (NZP.F k)) i = true := by
  intro k hk
  have h : npIK k = true := all_of_chunks 90 24 npNZS k hk
  unfold npIK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨hi, he⟩, hr⟩ := h
  dsimp only
  unfold npK
  rw [CFSG.KS.PinvS.pinvS_of_pcomp (pp_of_permB hw (nzp k hk)).1 (pp_of_permB hw (nzp _ hi)).1 he]
  exact hr

theorem enumNZ : enumOK 315 gensNZArr keyPts cNZ = true :=
  enumK_sound (G := GNZ) hw (by decide) gnz_size hgnz nz.1 nz.2.1 nz.2.2.1
    (fun i hi => nz.2.2.2 i hi) (by quickRfl) ptNZ_All kyNZ_All

theorem inNP {c : ℕ} (hc : permB 315 9 c = true) :
    inCert cNP (unpack 315 9 c) = memK 216 NPP.F c := by
  unfold inCert
  exact any_eqA_unpack hw np.1 np.2.1 npp hc

theorem npAll : chkNP = true := by
  unfold chkNP
  rw [allLt_iff, nz.1]
  intro k hk
  dsimp only
  have hp := nzp k hk
  rw [nz.2.1 k hk, hx, hy, conj_unpack hw hp pX, conj_unpack hw hp pY,
    inP3 (permB_pcomp hw hp (permB_pcomp hw pX (permB_pinvS hw hp))),
    inP3 (permB_pcomp hw hp (permB_pcomp hw pY (permB_pinvS hw hp))), inNP hp]
  exact npNZ_All k hk

theorem tenAll : chkTen = true := by
  unfold chkTen
  have h1 : allLt cNZ.pts.size (fun k => permutesSets s10Sets cNZ.pts[k]! &&
      (!fixesSets s10Sets cNZ.pts[k]! || inZ cNZ.pts[k]!)) = true := by
    rw [allLt_iff, nz.1]
    intro k hk
    rw [nz.2.1 k hk, permutes_sound hS10 hS10lt, fixes_sound hS10 hS10lt, inZ_unpack (nzp k hk)]
    exact tenNZ_All k hk
  have h2 : allLt gensNZArr.size (fun k => actsBy s10Sets gensNZArr[k]! (sigNZ.getD k [])) =
      true := by
    rw [allLt_iff, gnz_size]
    intro k hk
    have hσ : ∀ i < 10, (sigNZ.getD k []).getD i 0 < 10 := by
      interval_cases k <;> decide
    rw [hgnz k hk, acts_sound hS10 hS10lt hσ]
    interval_cases k <;> quickRfl
  rw [h1, h2]
  rfl

end CertificateChecks.KernelMisc.J2C3

end
