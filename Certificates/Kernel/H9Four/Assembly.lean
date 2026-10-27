module

public import Certificates.Kernel.H9Four.Checks
public import CFSG.Certificates.Kernel.H9Four.Sound

public section

namespace CFSG.KD.H9Four

open CFSG.Quasithin.H13.H9Four CFSG.KC.H9Four CFSG.KC.H9Four.Sound

theorem invL_complete (A : Fin 4 → Fin 4 → ZMod 2) (h1 : Matrix.of A * Matrix.of A = 1)
    (h2 : Matrix.of A ≠ 1) : ∃ k ∈ invLCodes, (Mat.ofCode k).toMatrix = Matrix.of A :=
  (walk_sound invLCodes invSCodes ch7104_walk).1 A h1 h2

theorem invS_complete (A : Fin 4 → Fin 4 → ZMod 2)
    (h1 : Matrix.transpose (Matrix.of A) = Matrix.of A) (h2 : (Matrix.of A).det ≠ 0) :
    ∃ p ∈ invSCodes, (Mat.ofCode p.1).toMatrix = Matrix.of A :=
  (walk_sound invLCodes invSCodes ch7104_walk).2 A h1 h2

theorem checkInv_true : checkInv = true := checkInv_sound invLCodes invSCodes ch7104_inv

theorem repCheck_true : repCheck = true := rep_sound repCodes repG repX ch7104_pin

theorem repCodes_length : repCodes.length = 29 := rfl

theorem closure_fact {i : ℕ} (hi : i < reps.length) {y : Elt} (hy : y ∈ invAll)
    (hc : (reps.getD i []).all (commutes y) = true)
    (hn : (elems (reps.getD i [])).contains y = false) :
    ∃ j < reps.length, ∃ c : Elt, c.valid = true ∧
      (reps.getD j []).length = (reps.getD i []).length + 1 ∧
      ∀ g ∈ reps.getD i [] ++ [y], (c.mul g).mul c.inv ∈ elems (reps.getD j []) :=
  clos_sound invLCodes invSCodes inv repCodes repG repX tab ch7104_inv ch7104_pinInv ch7104_pin
    (fun k hk => ch7104_rows k (hk.trans_eq repCodes_length)) hi hy hc hn

theorem rankCheck_true : rankCheck = true := rank_sound repCodes repG repX ch7104_pin ch7104_rank

theorem ffCheck16_true : ffCheckOf repCodes = true :=
  (invar_sound repCodes repG repX ch7104_pin ch7104_invar).1

theorem commCheck_true : commCheck = true :=
  (invar_sound repCodes repG repX ch7104_pin ch7104_invar).2.1

theorem centCheck_true : centCheck = true :=
  (invar_sound repCodes repG repX ch7104_pin ch7104_invar).2.2.1

theorem axesCheck_true : axesCheck = true :=
  (invar_sound repCodes repG repX ch7104_pin ch7104_invar).2.2.2

theorem e16Check_true : e16Check = true := e16_sound repCodes repG repX ch7104_pin ch7104_e16

end CFSG.KD.H9Four

end
