module

public import Certificates.Kernel.J2Dc.Defs
public import Certificates.Kernel.LocalQT.Base.C4142
public import CFSG.Certificates.Kernel.LocalQTBaseWProved
public import CFSG.Certificates.Kernel.E64FSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J2Dc

open CFSG.KC.E64F CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PP CFSG.KC.LQT.BC CFSG.KC.LQT.PW

@[expose] noncomputable def R : List ℕ :=
  slpW 315 9 (codeK 9 CFSG.KD.LQT.C4142.ta) (codeK 9 CFSG.KD.LQT.C4142.tb) j2Prog

theorem tcB : (J.tc == [codeK 9 CFSG.KD.LQT.C4142.ta, codeK 9 CFSG.KD.LQT.C4142.tb] ++
    ([155, 166, 179, 191, 192, 193].map fun j => nodeK R j)) = true := by
  quickRfl

theorem tabLa : tabL 315 CFSG.KD.LQT.C4142.ta = true := by quickRfl

theorem tabLb : tabL 315 CFSG.KD.LQT.C4142.tb = true := by quickRfl

theorem slpOK : slpOKK j2Prog 2 = true := by quickRfl

theorem tw_eq : J.tw = 9 := rfl

theorem L0_get (l : ℕ) : L0 l = imgW 9 (([codeK 9 CFSG.KD.LQT.C4142.ta,
    codeK 9 CFSG.KD.LQT.C4142.tb] ++ ([155, 166, 179, 191, 192, 193].map fun j => nodeK R j)).getD
    l 0) := by
  unfold L0
  rw [tw_eq, eq_of_beq tcB]

theorem rep_good {c : ℕ} {t : Array ℕ} (h : Rep 315 9 c t) : Good 315 t (imgW 9 c) :=
  ⟨h.1, fun p hp => ⟨(h.2 p hp).2.symm, (h.2 p hp).2 ▸ (h.2 p hp).1⟩⟩

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem rep_node {j : ℕ} (hj : j < j2Prog.length + 2) :
    Rep 315 9 (nodeK R j) (slpTabsA CFSG.KD.LQT.C4142.ta.toArray
      CFSG.KD.LQT.C4142.tb.toArray j2Prog)[j]! := by
  refine (slpW_rep (by norm_num) tabLa tabLb slpOK).2 j ?_
  rw [slpTabsA, slp_size]
  simpa [Nat.add_comm] using hj

theorem slp_lit : j2SLP = slpTabsA CFSG.KD.LQT.C4142.ta.toArray CFSG.KD.LQT.C4142.tb.toArray
    j2Prog := by
  rw [j2SLP, CFSG.KD.LQT.C4142.ta_eq, CFSG.KD.LQT.C4142.tb_eq]

theorem node_arr {j : ℕ} (hj : j < j2Prog.length + 2) :
    j2SLP[j]! = ((List.range 315).map (imgW 9 (nodeK R j))).toArray := by
  have h := rep_node hj
  rw [← slp_lit] at h
  refine Array.ext (by simp [h.1]) fun i h1 _ => ?_
  have hi : i < 315 := by rw [h.1] at h1; exact h1
  have e := (h.2 i hi).2
  rw [img, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some] at e
  rw [← e]
  simp

end CFSG.KD.J2Dc

end
