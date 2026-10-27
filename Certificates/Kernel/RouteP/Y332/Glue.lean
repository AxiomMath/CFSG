module

public import Certificates.Kernel.RouteP.Lines.Rep
public import Certificates.Kernel.RouteP.Lines.YL0
public import Certificates.Kernel.RouteP.Lines.YL1
public import Certificates.Kernel.RouteP.Y332.Check
public import CFSG.Certificates.Kernel.RouteP.TreeBFS
public import Certificates.Data.RouteP.Y332

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.Sporadic.LevelChain.Native
  CFSG.Perm.Native

#kc_forall_tree ylckL_all (fun g => CFSG.KD.RouteP.ylckL g = true) 2200 CFSG.KD.RouteP.ObjLC.y

theorem y332W_eq : y332LinesK = CFSG.KD.RouteP.ObjW.YL :=
  eq_of_beq (by decide +kernel : (y332LinesK == CFSG.KD.RouteP.ObjW.YL) = true)

theorem ylck_all : ∀ g < 2200, CFSG.KD.RouteP.ylck g = true := by
  intro g hg
  unfold CFSG.KD.RouteP.ylck
  rw [y332W_eq]
  exact ylckL_all g hg
#kc_forall_tree yck_all (fun g => CFSG.KD.RouteP.yck g = true) 940 CFSG.KD.RouteP.Y332Ck.y
#kc_forall_tree yfix_all (fun g => CFSG.KD.RouteP.yfix g = true) 18 CFSG.KD.RouteP.Y332Ck.f
#kc_forall_tree ybase_all (fun j => CFSG.KD.RouteP.ybase9 j = true) 62 CFSG.KD.RouteP.Y332Ck.b
#kc_forall_tree ylev_all (fun i => CFSG.KD.RouteP.ylev i = true) 8 CFSG.KD.RouteP.Y332Ck.l
#kc_forall_tree nkY_all (fun j => CFSG.KD.RouteP.nkY30 j = true) 82 CFSG.KD.RouteP.Y332Ck.n

noncomputable abbrev gY (r : Nat) : Perm Pt := gT NWY KAY KBY r

theorem lokY {z : ℤ} (hz : z.natAbs - 1 < 112) : LOK NWY KAY KBY z := by
  by_cases h : z.natAbs - 1 < 30
  · have e1 : NWY (z.natAbs - 1) = NWO (z.natAbs - 1) := by
      funext l
      unfold NWY
      rw [Nat.blt_eq.mpr h]
    have e2 : KAY (z.natAbs - 1) = KAO (z.natAbs - 1) := by
      unfold KAY
      rw [e1]
      rfl
    have e3 : KBY (z.natAbs - 1) = KBO (z.natAbs - 1) := by
      unfold KBY
      rw [e1]
      rfl
    have := lokO (z := z) (by omega)
    unfold LOK kapOK at *
    rw [e1, e2, e3]
    exact this
  · exact CFSG.KC.Benes.andB_true (by
      have h82 : z.natAbs - 1 - 30 < 82 := by omega
      have := nkY_all (z.natAbs - 1 - 30) h82
      unfold ybase9 nkY30 at this
      rwa [show z.natAbs - 1 - 30 + 30 = z.natAbs - 1 by omega] at this)

theorem y332Run_rep (hm : Rep 920808 (mTabs ())[0]! (gY 0) ∧ Rep 920808 (mTabs ())[1]! (gY 1)) :
    ∀ r < 112, Rep 920808 (y332Run ()).1[r]! (gY r) := by
  have hs := y332Lines_size
  intro r hr
  have := progRep_of (NW := NWY) (KA := KAY) (KB := KBY) y332Lines_eq (extra := 111) (by rw [hs]) hm
    y332Prog_ok y332Lines_linesOK (fun j hj => lokY (by simp; omega))
    (fun ℓ hℓ z hz => lokY ?_) (fun g hg => ylck_all g (by rw [hs] at hg; omega)) r (by rw [hs]; omega)
  · exact this
  · rw [← y332Lines_eq] at hz
    unfold lineW at hz
    obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
    have h1 := y332Lines_linesOK ℓ hℓ p (List.mem_reverse.1 hp)
    have := (List.mem_replicate.1 hz).2
    rw [hs] at hℓ
    split_ifs at this <;> subst this <;> simp <;> omega

end CertificateChecks.KernelRouteP

end
