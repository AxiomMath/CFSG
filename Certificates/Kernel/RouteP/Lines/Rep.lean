module

public import Certificates.Kernel.RouteP.Obj.Rep

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

theorem progRep_of {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {ls L : Array (List Int)} (hL : ls = L)
    {extra : Nat} (hext : extra = ls.size + 1)
    (hm : Rep 920808 (mTabs ())[0]! (gT NW KA KB 0) ∧ Rep 920808 (mTabs ())[1]! (gT NW KA KB 1))
    (hprog : progOK (2 + extra) (compileSLP 2 ls) = true) (hls : LinesOK 2 ls)
    (hlok : ∀ j < 2 + ls.size, LOK NW KA KB (Int.ofNat (j + 1)))
    (hw : ∀ ℓ < ls.size, ∀ z ∈ lineW 0 L[ℓ]!, LOK NW KA KB z)
    (hck : ∀ g < 20 * ls.size, lineOK NW KA KB L 0 (fun ℓ => 2 + ℓ) g = true) :
    ∀ r < 2 + ls.size, Rep 920808
      (runSLP degree (compileSLP 2 ls) (mTabs () ++ Array.replicate extra (idT degree))).1[r]!
      (gT NW KA KB r) := by
  have hn := hn32
  set regsG : ℕ → Perm Pt := fun r => if r < 2 then gT NW KA KB r else 1
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
      simp only [regsG, if_pos h2]
      rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
      · exact hm.1
      · exact hm.2
    · have e : regsT[r]! = idT degree := by
        rw [getElem!_pos _ r (by rw [hsize]; omega), Array.getElem_append_right (by omega)]
        simp
      rw [e]
      simp only [regsG, if_neg h2]
      exact Rep.idT hn
  have hprog' : ∀ ins ∈ compileSLP 2 ls, instrRegsLt regsT.size ins := by
    rw [hsize]
    exact instrRegsLt_of_progOK' hprog
  obtain ⟨-, -, hrep⟩ := runSLP_rep' hn (compileSLP 2 ls) regsT regsG hprog' hregs
  have hsz : L.size = ls.size := by rw [hL]
  have hlines := prog_spec (NW := NW) (KA := KA) (KB := KB) (g := 2) (o := 0) (ls := ls)
    (t := fun ℓ => 2 + ℓ) hls (regs := regsG) (fun r hr => by simp only [regsG, if_pos hr, Nat.add_zero])
    (fun ℓ hℓ => hlok _ (by omega))
    (fun ℓ hℓ z hz => by rw [hL] at hz; exact hw ℓ hℓ z hz)
    (fun ℓ hℓ k hk => by
      rw [hL]
      exact (lineOK_spec (fun k' hk' => hck (20 * ℓ + k') (by omega))).1 k hk)
    (fun ℓ hℓ => by
      rw [hL]
      exact (lineOK_spec (fun k' hk' => hck (20 * ℓ + k') (by omega))).2)
    (fun ℓ hℓ p hp hgp => by omega)
  intro r hr
  have h := hrep r (by rw [hsize]; omega)
  have e : runSLPG (compileSLP 2 ls) regsG r = gT NW KA KB r := by
    by_cases h2 : r < 2
    · rw [runSLPG_compileSLP_lt 2 _ hls regsG h2]
      simp only [regsG, if_pos h2]
    · have := hlines (r - 2) (by omega)
      rw [show 2 + (r - 2) = r by omega] at this
      exact this
  rw [e] at h
  exact h

end CertificateChecks.KernelRouteP

end
