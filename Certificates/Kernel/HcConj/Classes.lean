module

public import Certificates.Data.Kernel.HcConj
public import Certificates.Data.Kernel.HcClos
public import Certificates.Kernel.HcReplay.Elts
public import Certificates.Data.G23RecogHCharInputs
meta import CFSG.Certificates.Kernel.HcConjStep

public section

namespace CFSG.KC.HcPack

@[expose] def hcRP : List ℕ :=
  [1459980823972598128486511383358617792788444579872, 1415644244717357744752181898886272409354489712042,
    1132630522525786097437108122191548306319212556548, 1459489772190472173560349220849168662699482027105,
    1415197750828903055165529038006101970056559025293, 429161991104182283319765724322406958292896933102,
    945255251554321938218117011563967908082526897639, 429205940104968177943877639424412856904955938631,
    1459957104930169070366788001133702281052641597602, 1415619133240189561418123651908761848069376843507,
    1132612400448314380685982764030636893260701849228, 1459466053148750079268234941975840981864217131301,
    1415172639351652079233563252073429406361577962903, 1459778567992768319367995617343474443901048373321,
    1415485154237042459412837527887010883933575042668, 1459863811407222587774959023954699605037433754830,
    847429421418337430378441906407602617763516330901, 661090596761745285170372640675735123661814309759,
    705404896801898392327704156342435859614765985726, 761896439653309607658265352039605706456715733809]

@[expose] def hcIP : List ℕ := [3, 8, 11, 17]

end CFSG.KC.HcPack

#kc_eval CFSG.KC.HcPack hcCj CFSG.KC.HcPack.ConjStep.cjRec hcElts.E hcRP hcG hcIP

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23.HCharData

@[expose] noncomputable def hcL : List ℕ := hcCj.KF.flatten

@[expose] noncomputable def hcF (j : ℕ) : List ℕ := hcCj.KF.getD j []

@[expose] noncomputable def hcS (j : ℕ) : List ℕ := hcCj.KS.getD j []

theorem ch320017_class : ∀ j : Fin 20, cjClassP (hcRP.getD j 0) = (hcF j).zip (hcS j) := by
  decide +kernel

theorem ch320017_clos : ∀ j : Fin 20,
    posB (fun e x i => Nat.beq e (conjP (cjGP.getD i (0, 0)) x)) (getT (ofT (hcF j).length (hcF j)))
      (hcF j).length [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] (hcF j) (hcCj.dC.getD j []) = true := by
  decide +kernel

theorem ch320017_memF : ∀ j : Fin 20,
    posB (fun e x _ => Nat.beq e x) (getT (ofT 576 hcElts.E)) 576 [0] (hcF j)
      (hcCj.pF.getD j []) = true := by
  decide +kernel

theorem ch320017_memS : ∀ j : Fin 20,
    posB (fun e x _ => Nat.beq e x) (getT (ofT 576 hcElts.E)) 576 [0] (hcS j)
      (hcCj.pS.getD j []) = true := by
  decide +kernel

theorem ch320017_cover :
    posB (fun e x _ => Nat.beq e x) (getT (ofT 576 hcL)) 576 [0] hcElts.E hcCj.pL = true := by
  decide +kernel

theorem ch320017_nodup : hcCj.KF.length = 20 ∧ hcL.length = 576 ∧ hcCj.oL.length = 576 ∧
    incT (getT (ofT 576 hcL)) 576 hcCj.oL 0 = true ∧
    ∀ j : Fin 20, (hcF j).length = hcSize j ∧ (hcS j).length = hcSize j := by
  decide +kernel

theorem ch320017_inv : hcElts.E.length = 576 ∧
    posB (fun e x _ => Nat.beq e (invP x)) (getT (ofT 576 hcElts.E)) 576 [0] hcElts.E hcCj.pI =
      true := by
  decide +kernel

theorem ch320017_ord : ∀ j : Fin 20, powP (hcRP.getD j 0) (hcOrd j) = idP ∧
    ∀ m < hcOrd j, 0 < m → powP (hcRP.getD j 0) m ≠ idP := by
  decide +kernel

theorem ch320017_d : ∀ j : Fin 20, hcDfl j = true ↔
    (hcOrd j = 3 ∨ (hcOrd j % 2 = 0 ∧ powP (hcRP.getD j 0) (hcOrd j / 2) = hcRP.getD 1 0)) := by
  decide +kernel

theorem ch320017_ct :
    (hcElts.E.filter fun u => decide (mulP u u = idP ∧ u ≠ idP ∧ u ≠ hcRP.getD 1 0)).length =
      hcCt 1 ∧
    ∀ j : Fin 20, j ≠ 1 →
      (hcElts.E.filter fun u => decide (mulP u u = idP ∧ u ≠ idP ∧
        mulP u (hcRP.getD j 0) = mulP (invP (hcRP.getD j 0)) u)).length = hcCt j := by
  decide +kernel

theorem ch320017_a : ∀ r : Fin 4, ∀ k : Fin 20,
    hcIP.getD r 0 = (hcI r : ℕ) ∧
    ((hcCj.aC.getD r []).getD k []).length = (hcF (hcIP.getD r 0)).length ∧
    ∀ t < (hcF (hcIP.getD r 0)).length,
      ((hcCj.aC.getD r []).getD k []).getD t 0 < 20 ∧
      ((hcCj.aT.getD r []).getD k []).getD t 0 <
        (hcF (((hcCj.aC.getD r []).getD k []).getD t 0)).length ∧
      (hcF (((hcCj.aC.getD r []).getD k []).getD t 0)).getD
          (((hcCj.aT.getD r []).getD k []).getD t 0) 0 =
        mulP (invP ((hcF (hcIP.getD r 0)).getD t 0)) (hcRP.getD k 0) := by
  decide +kernel

theorem ch320017_count : ∀ r : Fin 4, ∀ k : Fin 20, ∀ j : Fin 20,
    ((hcCj.aC.getD r []).getD k []).count (j : ℕ) = hcA r j k := by
  decide +kernel

theorem ch320017_class_neg : cjClassP (hcRP.getD 15 0) ≠ (hcF 16).zip (hcS 15) := by
  decide +kernel

theorem ch320017_clos_neg :
    posB (fun e x i => Nat.beq e (conjP (cjGP.getD i (0, 0)) x)) (getT (ofT (hcF 15).length (hcF 15)))
      (hcF 15).length [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] (hcF 15) (0 :: (hcCj.dC.getD 15 []).tail) =
      false := by
  decide +kernel

end CFSG.KC.HcPack

end
