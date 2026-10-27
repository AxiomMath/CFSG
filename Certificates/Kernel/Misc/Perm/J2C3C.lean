
module

public import Certificates.Kernel.Misc.Perm.J2C3B
public import Certificates.Kernel.Misc.Perm.J2C3D
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.J2C3.NZP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZPHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZPHex
  3 315 9 2160
#ks_chars CertificateChecks.KernelMisc.J2C3.NZE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZEHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZEHex
  3 3 12 2160
#ks_chars CertificateChecks.KernelMisc.J2C3.NZR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZRHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZRHex
  3 2160 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.NZL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZLHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NZL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNZLHex
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
  permB 315 9 (pcomp 315 9 (mask 9) p (pcomp 315 9 (mask 9) X (pinvS 315 9 (mask 9) p))) &&
    permB 315 9 (pcomp 315 9 (mask 9) p (pcomp 315 9 (mask 9) Y (pinvS 315 9 (mask 9) p))) &&
    (!(memK 27 P3P.F (pcomp 315 9 (mask 9) p (pcomp 315 9 (mask 9) X (pinvS 315 9 (mask 9) p))) &&
        memK 27 P3P.F (pcomp 315 9 (mask 9) p (pcomp 315 9 (mask 9) Y (pinvS 315 9 (mask 9) p))))
      || memK 216 NPP.F p)

@[expose] noncomputable def tenK (p : ℕ) : Bool :=
  permutesK 10 9 9 S10 p &&
    (!fixesK 10 9 9 S10 p || (Nat.beq p I || Nat.beq p Z || Nat.beq p (cm Z Z)))

@[expose] noncomputable def ptNZC : ℕ → Bool :=
  chunkK 90 (pointK 315 9 3 2160 GNZ NZP.F (EF NZE.F) (VF NZR.F) (VF NZL.F))

@[expose] noncomputable def kyNZC : ℕ → Bool := chunkK 90 (keyF NZP.F)

@[expose] noncomputable def npNZC : ℕ → Bool := chunkK 90 fun k => npK (NZP.F k)

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
  all_of_chunks 90 24 ptNZS

theorem kyNZ_All : ∀ i < 2160, (keyF NZP.F) i = true := all_of_chunks 90 24 kyNZS

theorem npNZ_All : ∀ i < 2160, (fun k => npK (NZP.F k)) i = true := all_of_chunks 90 24 npNZS

theorem tenNZ_All : ∀ i < 2160, (fun k => tenK (NZP.F k)) i = true := all_of_chunks 90 24 tenNZS

theorem nzp (k : ℕ) (hk : k < 2160) : permB 315 9 (NZP.F k) = true := by
  have h := ptNZ_All k hk
  simp only [pointK, Bool.and_eq_true] at h
  exact h.1.1

theorem enumNZ : enumOK 315 gensNZArr keyPts cNZ = true :=
  enumK_sound (G := GNZ) hw (by decide) gnz_size hgnz nz.1 nz.2.1 nz.2.2.1
    (fun i hi => nz.2.2.2 i hi) (by quickRfl) ptNZ_All (keys_of_all kyNZ_All)

theorem inNP {c : ℕ} (hc : permB 315 9 c = true) :
    inCert cNP (unpack 315 9 c) = memK 216 NPP.F c := by
  unfold inCert
  exact any_eqA_unpack hw np.1 np.2.1 npp hc

theorem npAll : chkNP = true := by
  unfold chkNP
  rw [allLt_iff, nz.1]
  intro k hk
  dsimp only
  have h := npNZ_All k hk
  simp only [npK, Bool.and_eq_true] at h
  obtain ⟨⟨ha, hb⟩, hc⟩ := h
  rw [nz.2.1 k hk, hx, hy, conj_unpack hw (nzp k hk) pX, conj_unpack hw (nzp k hk) pY,
    inP3 ha, inP3 hb, inNP (nzp k hk)]
  exact hc

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
