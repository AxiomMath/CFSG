module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Inputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall
open CFSG.Quasithin.JonesParshall.Curtis
open scoped Matrix

theorem l52_cols :
    ∀ t : Fin 25, ∀ l : Fin 10,
      (fun k => wedgeMat ((trSL' t : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l) =
        decodeV (l52Col.getD (10 * t + l) 0) := by
  decide +kernel

theorem l52_cert :
    ∀ c < 1024, c ≠ 0 →
      applyC (l52Words.getD c []) (l52BaseC (l52Cls.getD c false)) = c ∧
        ∀ t ∈ l52Words.getD c [], t < 25 := by
  decide +kernel

theorem l52_count_true :
    (Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = true).card = 155 := by
  decide +kernel

theorem l52_count_false :
    (Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = false).card =
      868 := by
  decide +kernel

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall in
open CFSG.Quasithin.JonesParshall.Curtis in
open scoped Matrix in
theorem c7053 :
    (∀ t : Fin 25, ∀ l : Fin 10,
       (fun k => wedgeMat ((trSL' t : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l) =
         decodeV (l52Col.getD (10 * t + l) 0))
    ∧ (∀ c < 1024, c ≠ 0 →
       applyC (l52Words.getD c []) (l52BaseC (l52Cls.getD c false)) = c ∧
         ∀ t ∈ l52Words.getD c [], t < 25)
    ∧ ((Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = true).card = 155)
    ∧ ((Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = false).card =
       868) :=
  ⟨l52_cols, l52_cert, l52_count_true, l52_count_false⟩

end CertificateChecks.KernelJ4F2

end
