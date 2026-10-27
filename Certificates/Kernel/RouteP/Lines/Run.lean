module

public import Certificates.Kernel.RouteP.Cocode.Glue

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

theorem mRun_flag {g0 g1 : Perm Pt} {extra : Nat} {prog : List Instr}
    (hm : Rep 920808 (mTabs ())[0]! g0 ∧ Rep 920808 (mTabs ())[1]! g1)
    (hprog : progOK (2 + extra) prog = true) :
    (runSLP degree prog (mTabs () ++ Array.replicate extra (idT degree))).2 = true ∧
      (runSLP degree prog (mTabs () ++ Array.replicate extra (idT degree))).1.size = 2 + extra := by
  have hn := hn32
  set regsG : ℕ → Perm Pt := fun r => if r = 0 then g0 else if r = 1 then g1 else 1
  set regsT := mTabs () ++ Array.replicate extra (idT degree)
  have hm2 : (mTabs ()).size = 2 := rfl
  have hsize : regsT.size = 2 + extra := by
    simp only [regsT, Array.size_append, Array.size_replicate, hm2]
  have hregs : ∀ r < regsT.size, Rep 920808 regsT[r]! (regsG r) := by
    intro r hr
    rw [hsize] at hr
    by_cases h2 : r < 2
    · have e : regsT[r]! = (mTabs ())[r]! := by
        rw [getElem!_pos _ r (by rw [hsize]; omega), getElem!_pos (mTabs ()) r (by omega),
          Array.getElem_append_left]
      rw [e]
      rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
      · exact hm.1
      · exact hm.2
    · have e : regsT[r]! = idT degree := by
        rw [getElem!_pos _ r (by rw [hsize]; omega), Array.getElem_append_right (by omega)]
        simp
      rw [e]
      simp only [regsG, if_neg (by omega : r ≠ 0), if_neg (by omega : r ≠ 1)]
      exact Rep.idT hn
  have hprog' : ∀ ins ∈ prog, instrRegsLt regsT.size ins := by
    rw [hsize]
    exact instrRegsLt_of_progOK' hprog
  obtain ⟨h1, h2, -⟩ := runSLP_rep' hn prog regsT regsG hprog' hregs
  exact ⟨h1, h2.trans hsize⟩

end CertificateChecks.KernelRouteP

end
