module

public import Certificates.Data.Kernel.DcK

public section

namespace CFSG.KD.HS589207

open CFSG.KC.DcK

theorem elemsK_add (n : Nat) (B : List Nat) (G : Nat → Nat → Nat) (m : Nat) (E : EnumK)
    (lo a b : Nat) :
    elemsK n B G m E lo (a + b) = (elemsK n B G m E lo a && elemsK n B G m E (lo + a) b) := by
  unfold elemsK
  rw [← List.range'_append_1, List.all_append]

theorem elemsK_4 (n : Nat) (B : List Nat) (G : Nat → Nat → Nat) (m : Nat) (E : EnumK)
    (lo q : Nat) :
    elemsK n B G m E lo (q + q + q + q) = (elemsK n B G m E lo q &&
      (elemsK n B G m E (lo + q) q && (elemsK n B G m E (lo + q + q) q &&
        elemsK n B G m E (lo + q + q + q) q))) := by
  rw [show q + q + q + q = q + (q + (q + q)) by omega, elemsK_add, elemsK_add, elemsK_add]

end CFSG.KD.HS589207

end
