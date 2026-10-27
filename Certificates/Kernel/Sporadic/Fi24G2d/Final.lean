module

public import Certificates.Kernel.Sporadic.Fi24G2d.C2C
public import Certificates.Kernel.Sporadic.Fi24G2d.C2A
public import Certificates.Kernel.Sporadic.Fi24G2d.C2D
public import Certificates.Kernel.Sporadic.Fi24G2d.C2B
public import Certificates.Kernel.Sporadic.Fi24G2d.L
public import CFSG.Certificates.Kernel.Spor.Fi24G2dSound

public section

namespace CFSG.KD.Fi24G2d

open CFSG.KC.Fi24FixK CFSG.KC.Fi24G2d CFSG.KC.Fi24G2dS

theorem chunks2C : ∀ c < 74, Nat.beq (cntFix idN CFSG.KD.Fi24Fix.TG WN W2C (4096 * c) 4096 64)
    (K2C.getD c 0) = true := C2C.all

theorem chunks2A : ∀ c < 74, Nat.beq (cntFix idN CFSG.KD.Fi24Fix.TG WN W2A (4096 * c) 4096 64)
    (K2A.getD c 0) = true := C2A.all

theorem chunks2D : ∀ c < 74, Nat.beq (cntFix idN CFSG.KD.Fi24Fix.TG WN W2D (4096 * c) 4096 64)
    (K2D.getD c 0) = true := C2D.all

theorem chunks2B : ∀ c < 74, Nat.beq (cntFix idN CFSG.KD.Fi24Fix.TG WN W2B (4096 * c) 4096 64)
    (K2B.getD c 0) = true := C2B.all

theorem card_fix_W2C :
    ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG W2C r = r).card = 31672 := by
  rw [card_fix_of_chunks _ _ K2C chunks2C C2C.last]
  decide

theorem card_fix_W2A :
    ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG W2A r = r).card = 3512 := by
  rw [card_fix_of_chunks _ _ K2A chunks2A C2A.last]
  decide

theorem card_fix_W2D :
    ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG W2D r = r).card = 696 := by
  rw [card_fix_of_chunks _ _ K2D chunks2D C2D.last]
  decide

theorem card_fix_W2B :
    ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG W2B r = r).card = 504 := by
  rw [card_fix_of_chunks _ _ K2B chunks2B C2B.last]
  decide

theorem F2D_spec : ∀ j < 696, F2D j < 306936 ∧ walk CFSG.KD.Fi24Fix.TG W2D (F2D j) = F2D j ∧
    (j + 1 < 696 → F2D j < F2D (j + 1)) :=
  fixLOK_spec L.l2D (by omega)

theorem F2B_spec : ∀ j < 504, F2B j < 306936 ∧ walk CFSG.KD.Fi24Fix.TG W2B (F2B j) = F2B j ∧
    (j + 1 < 504 → F2B j < F2B (j + 1)) :=
  fixLOK_spec L.l2B (by omega)

theorem F2D_lt : ∀ j, j + 1 < 696 → F2D j < F2D (j + 1) := fun j hj =>
  (F2D_spec j (by omega)).2.2 hj

theorem F2B_lt : ∀ j, j + 1 < 504 → F2B j < F2B (j + 1) := fun j hj =>
  (F2B_spec j (by omega)).2.2 hj

theorem fix_W2D_iff : ∀ r < 306936, walk CFSG.KD.Fi24Fix.TG W2D r = r ↔ ∃ j < 696, F2D j = r :=
  fix_iff_of_list F2D_spec card_fix_W2D

theorem fix_W2B_iff : ∀ r < 306936, walk CFSG.KD.Fi24Fix.TG W2B r = r ↔ ∃ j < 504, F2B j = r :=
  fix_iff_of_list F2B_spec card_fix_W2B

end CFSG.KD.Fi24G2d

end
