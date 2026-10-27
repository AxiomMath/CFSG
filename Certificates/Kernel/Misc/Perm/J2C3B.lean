
module

public import Certificates.Kernel.Misc.Perm.J2C3A
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KC.Misc.Clos (allN_iff allR forall_of_chunks)

@[expose] noncomputable def keyF (F : ℕ → ℕ) (i : ℕ) : Bool :=
  CFSG.KC.LQT.P.allN i fun j => !(Nat.beq (keyK 315 9 keyPts (F i)) (keyK 315 9 keyPts (F j)))

theorem keys_of_all {N : ℕ} {F : ℕ → ℕ} (h : ∀ i < N, keyF F i = true) :
    ∀ i < N, ∀ j < i, keyK 315 9 keyPts (F i) ≠ keyK 315 9 keyPts (F j) := by
  intro i hi j hj he
  have h2 := (allN_iff _ _).1 (h i hi) j hj
  rw [he, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

@[expose] noncomputable def EF (FE : ℕ → ℕ) (i k : ℕ) : ℕ := pg 12 (mask 12) (FE i) k

@[expose] noncomputable def VF (FR : ℕ → ℕ) (i : ℕ) : ℕ := pg 12 (mask 12) (FR 0) i

@[expose] noncomputable def GXY (k : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) X (fun _ _ => Y) k

@[expose] noncomputable def GXYH (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) X (fun j _ => Nat.rec (motive := fun _ => ℕ) Y (fun _ _ => H8) j) k

@[expose] noncomputable def chunkK (s : ℕ) (f : ℕ → Bool) (c : ℕ) : Bool := allR (s * c) s f

theorem all_of_chunks (s m : ℕ) {f : ℕ → Bool} (h : ∀ c < m, chunkK s f c = true) :
    ∀ i < s * m, f i = true :=
  forall_of_chunks s m f h

@[expose] noncomputable def ptCzC : ℕ → Bool :=
  chunkK 90 (pointK 315 9 2 1080 GC CzP.F (EF CzE.F) (VF CzR.F) (VF CzL.F))

@[expose] noncomputable def kyCzC : ℕ → Bool := chunkK 90 (keyF CzP.F)

@[expose] noncomputable def ptNPC : ℕ → Bool :=
  chunkK 54 (pointK 315 9 3 216 GXYH NPP.F (EF NPE.F) (VF NPR.F) (VF NPL.F))

@[expose] noncomputable def kyNPC : ℕ → Bool := chunkK 54 (keyF NPP.F)

end CertificateChecks.KernelMisc.J2C3

#kc_each CertificateChecks.KernelMisc.J2C3.ptCzC 0 12
#kc_each CertificateChecks.KernelMisc.J2C3.kyCzC 0 12
#kc_each CertificateChecks.KernelMisc.J2C3.ptNPC 0 4
#kc_each CertificateChecks.KernelMisc.J2C3.kyNPC 0 4

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.RankThree.Native
open CFSG.KC.Misc.Clos (allR forall_of_chunks)

#kc_forall_chunks ptCzS (fun c => ptCzC c = true) 12 CertificateChecks.KernelMisc.J2C3.ptCzC 1
#kc_forall_chunks kyCzS (fun c => kyCzC c = true) 12 CertificateChecks.KernelMisc.J2C3.kyCzC 1
#kc_forall_chunks ptNPS (fun c => ptNPC c = true) 4 CertificateChecks.KernelMisc.J2C3.ptNPC 1
#kc_forall_chunks kyNPS (fun c => kyNPC c = true) 4 CertificateChecks.KernelMisc.J2C3.kyNPC 1

theorem ptP3_All : ∀ i < 27,
    (pointK 315 9 2 27 GXY P3P.F (EF P3E.F) (VF P3R.F) (VF P3L.F)) i = true :=
  forall_of_chunks 27 1 _ fun c hc => by
    obtain rfl : c = 0 := by omega
    quickRfl

theorem kyP3_All : ∀ i < 27, (keyF P3P.F) i = true :=
  forall_of_chunks 27 1 _ fun c hc => by
    obtain rfl : c = 0 := by omega
    quickRfl

theorem ptCz_All : ∀ i < 1080,
    (pointK 315 9 2 1080 GC CzP.F (EF CzE.F) (VF CzR.F) (VF CzL.F)) i = true :=
  all_of_chunks 90 12 ptCzS

theorem kyCz_All : ∀ i < 1080, (keyF CzP.F) i = true := all_of_chunks 90 12 kyCzS

theorem ptNP_All : ∀ i < 216,
    (pointK 315 9 3 216 GXYH NPP.F (EF NPE.F) (VF NPR.F) (VF NPL.F)) i = true :=
  all_of_chunks 54 4 ptNPS

theorem kyNP_All : ∀ i < 216, (keyF NPP.F) i = true := all_of_chunks 54 4 kyNPS

theorem enumP3 : enumOK 315 gensP3 keyPts cP3 = true :=
  enumK_sound (G := GXY) hw (by decide) (by rfl) (fun k hk => by
      interval_cases k
      · exact hx
      · exact hy)
    p3.1 p3.2.1 p3.2.2.1 (fun i hi => p3.2.2.2 i hi) (by quickRfl) ptP3_All
    (keys_of_all kyP3_All)

theorem enumCz : enumOK 315 gensCzArr keyPts cCz = true :=
  enumK_sound (G := GC) hw (by decide) gcz_size hgc cz.1 cz.2.1 cz.2.2.1
    (fun i hi => cz.2.2.2 i hi) (by quickRfl) ptCz_All (keys_of_all kyCz_All)

theorem enumNP : enumOK 315 gensNP keyPts cNP = true :=
  enumK_sound (G := GXYH) hw (by decide) (by rfl) (fun k hk => by
      interval_cases k
      · exact hx
      · exact hy
      · exact hh8)
    np.1 np.2.1 np.2.2.1 (fun i hi => np.2.2.2 i hi) (by quickRfl) ptNP_All
    (keys_of_all kyNP_All)

end CertificateChecks.KernelMisc.J2C3

end
