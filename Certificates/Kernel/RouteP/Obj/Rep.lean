module

public import Certificates.Kernel.RouteP.Cocode.Glue

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

theorem lineOK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {L : Array (List Int)} {o : Nat}
    {t : Nat → Nat} {ℓ : Nat} (h : ∀ k < 20, lineOK NW KA KB L o t (20 * ℓ + k) = true) :
    (∀ k < 19, CFSG.KC.RouteP.wordOK NW (lineW o L[ℓ]!) (t ℓ) k = true) ∧
      wordKOK NW KA KB (lineW o L[ℓ]!) (t ℓ) = true := by
  refine ⟨fun k hk => ?_, ?_⟩
  · have e := h k (by omega)
    unfold lineOK at e
    have e1 : Nat.mod (20 * ℓ + k) 20 = k := by change (20 * ℓ + k) % 20 = k; omega
    have e2 : Nat.div (20 * ℓ + k) 20 = ℓ := by change (20 * ℓ + k) / 20 = ℓ; omega
    rw [e1, e2, Nat.blt_eq.mpr hk] at e
    exact e
  · have e := h 19 (by omega)
    unfold lineOK at e
    have e1 : Nat.mod (20 * ℓ + 19) 20 = 19 := by change (20 * ℓ + 19) % 20 = 19; omega
    have e2 : Nat.div (20 * ℓ + 19) 20 = ℓ := by change (20 * ℓ + 19) / 20 = ℓ; omega
    rw [e1, e2, show Nat.blt 19 19 = false from rfl] at e
    exact e

theorem objRep_of {L : Array (List Int)} (hL : objLines () = L)
    (hm : Rep 920808 (mTabs ())[0]! (gO 0) ∧ Rep 920808 (mTabs ())[1]! (gO 1))
    (hprog : progOK 59 (objProg ()) = true) (hls : LinesOK 2 (objLines ())) (hsz : L.size = 56)
    (hw : ∀ ℓ < 56, ∀ z ∈ lineW 0 L[ℓ]!, z.natAbs - 1 < 58)
    (hck : ∀ g < 1120, lineOK NWO KAO KBO L 0 (fun ℓ => 2 + ℓ) g = true) :
    ∀ r < 58, Rep 920808 (objRun ()).1[r]! (gO r) := by
  have hn := hn32
  set regsG : ℕ → Perm Pt := fun r => if r < 2 then gO r else 1
  have hsize : (objRegs ()).size = 59 := by
    unfold objRegs
    rw [Array.size_append, Array.size_replicate]
    rfl
  have hregs : ∀ r < (objRegs ()).size, Rep 920808 (objRegs ())[r]! (regsG r) := by
    intro r hr
    rw [hsize] at hr
    unfold objRegs
    by_cases h2 : r < 2
    · have e : (mTabs () ++ Array.replicate 57 (idT degree))[r]! = (mTabs ())[r]! := by
        rw [getElem!_pos _ r (by simp [mTabs]; omega), getElem!_pos (mTabs ()) r (by simp [mTabs]; omega),
          Array.getElem_append_left]
      rw [e]
      simp only [regsG, if_pos h2]
      rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
      · exact hm.1
      · exact hm.2
    · have e : (mTabs () ++ Array.replicate 57 (idT degree))[r]! = idT degree := by
        rw [getElem!_pos _ r (by simp [mTabs]; omega), Array.getElem_append_right (by simp [mTabs]; omega)]
        simp
      rw [e]
      simp only [regsG, if_neg h2]
      exact Rep.idT hn
  have hprog' : ∀ ins ∈ objProg (), instrRegsLt (objRegs ()).size ins := by
    rw [hsize]
    exact instrRegsLt_of_progOK' hprog
  obtain ⟨-, -, hrep⟩ := runSLP_rep' hn (objProg ()) (objRegs ()) regsG hprog' hregs
  have hsz' : (objLines ()).size = 56 := by rw [hL]; exact hsz
  have hlines := prog_spec (NW := NWO) (KA := KAO) (KB := KBO) (g := 2) (o := 0) (ls := objLines ())
    (t := fun ℓ => 2 + ℓ) hls (regs := regsG) (fun r hr => by simp only [regsG, if_pos hr, Nat.add_zero])
    (fun ℓ hℓ => lokO (by simp; omega))
    (fun ℓ hℓ z hz => lokO (by rw [hL] at hz; exact hw ℓ (by omega) z hz))
    (fun ℓ hℓ k hk => by
      rw [hL]
      exact (lineOK_spec (fun k' hk' => hck (20 * ℓ + k') (by rw [hsz'] at hℓ; omega))).1 k hk)
    (fun ℓ hℓ => by
      rw [hL]
      exact (lineOK_spec (fun k' hk' => hck (20 * ℓ + k') (by rw [hsz'] at hℓ; omega))).2)
    (fun ℓ hℓ p hp hgp => by omega)
  intro r hr
  have h := hrep r (by rw [hsize]; omega)
  have e : runSLPG (objProg ()) regsG r = gO r := by
    by_cases h2 : r < 2
    · unfold objProg
      rw [runSLPG_compileSLP_lt 2 _ hls regsG h2]
      simp only [regsG, if_pos h2]
    · have := hlines (r - 2) (by rw [hsz']; omega)
      rw [show 2 + (r - 2) = r by omega] at this
      unfold objProg
      exact this
  rw [e] at h
  exact h

end CertificateChecks.KernelRouteP

end
