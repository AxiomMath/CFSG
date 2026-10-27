module

public import Certificates.Data.Kernel.KDenseP.Chunk

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense CFSG.Monster.AxisCount

theorem chunkOKN_loc {n lg q : Nat} {F : Fix} {MT : MonoTab} {WL : Nat → List Native.Gen} :
    ∀ (S S' : Nat → St) (c : Nat), S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) →
      chunkOKN n lg q F MT WL S c = chunkOKN n lg q F MT WL S' c := by
  intro S S' c h3 h4
  unfold chunkOKN
  rw [h3, h4]

theorem chunkOKN_prod {n lg q : Nat} {F : Fix} {MT : MonoTab} {WL : Nat → List Native.Gen} :
    ∀ (S : Nat → St) (c : Nat), Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      chunkOKN n lg q F MT WL S c = stEqN n (runN n lg F MT (WL (f20 c (nat_lit 0)))
        (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))) := by
  intro S c h
  unfold chunkOKN
  rw [h]

end CFSG.KC.KDenseP

end
